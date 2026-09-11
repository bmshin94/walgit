//! Metadata publication for already committed packs. Graph closure/conservation
//! must be proved by the producer; these guards validate the authority structure.
use crate::{CoverageSnapshot, RepoHandle, WalError};
use prost::Message;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use walgit_proto::v1::{Manifest, PackAudience, PackGroupCoverage, PackKind, PackRef};
use walgit_store::{ObjectStore, PutBody, PutMode, StoreError};

#[derive(Clone, Debug, Default)]
pub struct PackClassification {
    pub checksum: String,
    pub kind: i32,
    pub audience: i32,
    pub ref_policy: String,
    pub pack_groups: Vec<String>,
    pub covers_seq: u64,
    pub coverage_refs_key: String,
    pub group_coverages: Vec<PackGroupCoverage>,
}

impl PackClassification {
    pub fn from_pack(pack: &PackRef) -> Self {
        Self {
            checksum: pack.checksum.clone(),
            kind: pack.kind,
            audience: pack.audience,
            ref_policy: pack.ref_policy.clone(),
            pack_groups: pack.pack_groups.clone(),
            covers_seq: pack.covers_seq,
            coverage_refs_key: pack.coverage_refs_key.clone(),
            group_coverages: pack.group_coverages.clone(),
        }
    }

    pub(crate) fn apply(&self, pack: &mut PackRef) {
        pack.kind = self.kind;
        pack.audience = self.audience;
        pack.ref_policy.clone_from(&self.ref_policy);
        pack.pack_groups.clone_from(&self.pack_groups);
        pack.covers_seq = self.covers_seq;
        pack.coverage_refs_key.clone_from(&self.coverage_refs_key);
        pack.group_coverages.clone_from(&self.group_coverages);
    }
}

fn invalid(message: impl Into<String>) -> WalError {
    WalError::Invalid(message.into())
}

/// Removing/reclassifying inputs revokes surviving certificates that no longer
/// describe a complete set. It does not delete their packs or rewrite bytes.
pub(crate) fn prune_invalid_coverages(
    manifest: &mut Manifest,
    cfg: &walgit_config::Config,
    changed: &[String],
) {
    let policy = cfg.refs.policy_identity();
    loop {
        let before = manifest.clone();
        let mut removed = false;
        for carrier in &mut manifest.packs {
            if changed.contains(&carrier.checksum) {
                continue;
            }
            carrier.group_coverages.retain(|proof| {
                let valid = proof.ref_policy == policy
                    && cfg.refs.packfiles.get(&proof.group).is_some_and(|group| {
                        !proof.packs.is_empty()
                            && proof.packs.iter().all(|id| {
                                before.packs.iter().any(|p| {
                                    p.checksum == *id
                                        && p.pack_groups.contains(&proof.group)
                                        && p.ref_policy == policy
                                        && p.covers_seq == proof.covers_seq
                                        && p.coverage_refs_key == proof.refs_key
                                })
                            })
                            && group.subtract.iter().all(|dependency| {
                                before
                                    .packs
                                    .iter()
                                    .flat_map(|p| &p.group_coverages)
                                    .any(|c| {
                                        c.group == *dependency
                                            && c.ref_policy == policy
                                            && c.covers_seq == proof.covers_seq
                                            && c.refs_key == proof.refs_key
                                    })
                            })
                    });
                removed |= !valid;
                valid
            });
        }
        if !removed {
            break;
        }
    }
}

/// One validator for COMPACT and metadata CAS attempts. Candidates have no
/// authority before this CAS; existing snapshot keys must already be committed.
pub(crate) async fn validate_certificates(
    handle: &RepoHandle,
    before: &Manifest,
    after: &Manifest,
    changed: &[String],
    candidates: &[CoverageSnapshot],
) -> Result<(), WalError> {
    let cfg = handle.validated_config_for_manifest(before)?;
    let policy = cfg.refs.policy_identity();
    let live: BTreeMap<&str, &PackRef> = after
        .packs
        .iter()
        .map(|p| (p.checksum.as_str(), p))
        .collect();
    let proofs: Vec<&PackGroupCoverage> = after
        .packs
        .iter()
        .flat_map(|p| &p.group_coverages)
        .collect();
    let mut validated = BTreeSet::new();
    let mut snapshots: BTreeMap<String, walgit_proto::v1::RefSnapshot> = BTreeMap::new();
    for checksum in changed {
        let pack = live
            .get(checksum.as_str())
            .ok_or_else(|| invalid("classified pack is no longer live"))?;
        if PackKind::try_from(pack.kind).is_err() || PackAudience::try_from(pack.audience).is_err()
        {
            return Err(invalid("unknown pack classification"));
        }
        let unique: BTreeSet<_> = pack.pack_groups.iter().collect();
        if unique.len() != pack.pack_groups.len() {
            return Err(invalid("duplicate pack group"));
        }
        for group in &pack.pack_groups {
            if group == "_retained" {
                if pack.audience != PackAudience::Retained as i32
                    || !pack.group_coverages.is_empty()
                {
                    return Err(invalid("retained packs cannot carry group coverage"));
                }
                continue;
            }
            let definition = cfg
                .refs
                .packfiles
                .get(group)
                .ok_or_else(|| invalid(format!("unknown pack group {group}")))?;
            let audience = match definition.kind {
                walgit_config::PackGroupKind::Code => PackAudience::Code,
                walgit_config::PackGroupKind::Meta => PackAudience::Meta,
            };
            if pack.ref_policy != policy || pack.audience != audience as i32 {
                return Err(invalid(
                    "pack classification has stale policy or wrong audience",
                ));
            }
        }
        for coverage in &pack.group_coverages {
            if !pack.pack_groups.contains(&coverage.group)
                || pack.coverage_refs_key != coverage.refs_key
                || !coverage.packs.contains(&pack.checksum)
            {
                return Err(invalid("coverage carrier is outside its certificate"));
            }
            let mut pending = vec![coverage];
            while let Some(proof) = pending.pop() {
                if !validated.insert((
                    proof.group.clone(),
                    proof.covers_seq,
                    proof.refs_key.clone(),
                    proof.packs.clone(),
                )) {
                    continue;
                }
                if proof.ref_policy != policy
                    || proof.covers_seq > before.head_seq
                    || proof.refs_key.is_empty()
                {
                    return Err(invalid("coverage policy or captured generation is invalid"));
                }
                let definition = cfg
                    .refs
                    .packfiles
                    .get(&proof.group)
                    .ok_or_else(|| invalid("coverage names an unknown group"))?;
                let members: BTreeSet<_> = proof.packs.iter().collect();
                if members.is_empty() || members.len() != proof.packs.len() {
                    return Err(invalid("coverage members are empty or duplicated"));
                }
                for member in &proof.packs {
                    let p = live
                        .get(member.as_str())
                        .ok_or_else(|| invalid(format!("coverage member {member} is not live")))?;
                    if !p.pack_groups.contains(&proof.group)
                        || p.ref_policy != policy
                        || p.covers_seq != proof.covers_seq
                        || p.coverage_refs_key != proof.refs_key
                    {
                        return Err(invalid("coverage member scope changed"));
                    }
                    let expected = match definition.kind {
                        walgit_config::PackGroupKind::Code => PackAudience::Code,
                        walgit_config::PackGroupKind::Meta => PackAudience::Meta,
                    };
                    if p.audience != expected as i32 {
                        return Err(invalid("coverage member audience changed"));
                    }
                }
                let snapshot = if let Some(cached) = snapshots.get(&proof.refs_key) {
                    cached.clone()
                } else if let Some(candidate) = candidates.iter().find(|s| s.key == proof.refs_key)
                {
                    if candidate.repo != before.repo {
                        return Err(invalid("coverage candidate belongs to another repository"));
                    }
                    candidate.snapshot.clone()
                } else {
                    let committed = before
                        .packs
                        .iter()
                        .flat_map(|p| &p.group_coverages)
                        .any(|p| p.refs_key == proof.refs_key && p.covers_seq == proof.covers_seq)
                        || before.checkpoint.as_ref().is_some_and(|cp| {
                            cp.refs_key == proof.refs_key && cp.seq == proof.covers_seq
                        });
                    if !committed {
                        return Err(invalid(
                            "coverage snapshot is not committed or supplied by its producer",
                        ));
                    }
                    crate::snapshots::read_snapshot(
                        &handle.store,
                        &proof.refs_key,
                        proof.covers_seq,
                        &before.object_format,
                    )
                    .await?
                };
                snapshots.insert(proof.refs_key.clone(), snapshot.clone());
                if snapshot.seq != proof.covers_seq
                    || snapshot.object_format != before.object_format
                {
                    return Err(invalid("coverage snapshot generation mismatch"));
                }
                for dependency in &definition.subtract {
                    let dependency_proof = proofs
                        .iter()
                        .find(|p| {
                            p.group == *dependency
                                && p.covers_seq == proof.covers_seq
                                && p.refs_key == proof.refs_key
                                && p.ref_policy == policy
                        })
                        .ok_or_else(|| {
                            invalid(format!(
                                "missing same-generation coverage for dependency {dependency}"
                            ))
                        })?;
                    if proofs.iter().any(|p| {
                        p.group == *dependency
                            && p.covers_seq == proof.covers_seq
                            && p.refs_key == proof.refs_key
                            && p.ref_policy == policy
                            && p.packs != dependency_proof.packs
                    }) {
                        return Err(invalid("conflicting dependency coverage"));
                    }
                    pending.push(*dependency_proof);
                }
            }
        }
    }
    Ok(())
}

impl RepoHandle {
    /// Reclassify a bounded batch without changing WAL sequence or pack bytes.
    /// Every retry proves membership and policy against its fresh CAS basis.
    pub async fn reclassify_packs(
        &self,
        changes: &[PackClassification],
        candidates: &[CoverageSnapshot],
    ) -> Result<(), WalError> {
        if changes.is_empty() {
            return Ok(());
        }
        if changes.len() > 128 || candidates.len() > 128 {
            return Err(invalid("classification batch exceeds 128"));
        }
        let ids: Vec<_> = changes.iter().map(|c| c.checksum.clone()).collect();
        if ids.iter().collect::<BTreeSet<_>>().len() != ids.len() {
            return Err(invalid("duplicate classification checksum"));
        }
        for attempt in 0..self.cfg.wal.cas_max_retries {
            self.sync_impl_level(crate::SyncLevel::Refs).await?;
            let (current, version) = self.manifest_pair();
            let mut updated = (*current).clone();
            for change in changes {
                let pack = updated
                    .packs
                    .iter_mut()
                    .find(|p| p.checksum == change.checksum)
                    .ok_or_else(|| invalid("classification input was retired"))?;
                change.apply(pack);
            }
            let cfg = self.validated_config_for_manifest(&current)?;
            prune_invalid_coverages(&mut updated, &cfg, &ids);
            validate_certificates(self, &current, &updated, &ids, candidates).await?;
            updated.revision += 1;
            updated.updated_at = Some(walgit_proto::time::now());
            updated.writer = crate::handle::instance_id();
            let mode = version.map_or(PutMode::Create, PutMode::Update);
            match self
                .store
                .put(
                    walgit_proto::keys::MANIFEST,
                    PutBody::Bytes(updated.encode_to_vec().into()),
                    mode.into(),
                )
                .await
            {
                Ok(meta) => {
                    let _sync = self.sync_mutex.lock().await;
                    if self.adopt_manifest(Arc::new(updated.clone()), meta.version.clone()) {
                        let mut state = self.state.lock();
                        state.manifest_version = Some(meta.version.as_str().to_string());
                        state.revision = updated.revision;
                    }
                    return Ok(());
                }
                Err(StoreError::PreconditionFailed { .. }) => {
                    tokio::time::sleep(std::time::Duration::from_millis(
                        5 + u64::from(attempt) * 7,
                    ))
                    .await;
                }
                Err(e) => return Err(e.into()),
            }
        }
        Err(WalError::Retry {
            attempts: self.cfg.wal.cas_max_retries,
        })
    }
}
