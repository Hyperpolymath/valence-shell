# Valence Shell (vsh)

## Project Overview

**Formally verified shell implementing MAA (Mutually Assured Accountability) Framework.**

**Goal**: Every operation backed by machine-checkable proofs, enabling GDPR compliance with mathematical certainty.

**Current Phase**: Research and proof-of-concept. Abstract proofs complete, implementation unverified.

## Repository Information

**Primary Repository**: https://gitlab.com/non-initiate/rhodinised/vsh (GitLab)

**This Repository**: Hyperpolymath/valence-shell (GitHub - working copy/handover location)

**Note for AI Assistants**: Main development happens on GitLab. This GitHub repo may be a temporary workspace or migration staging area.

## Current State (as of 2025-11-21)

### ✅ Formal Proofs (Complete - Abstract Models Only)

- `proofs/coq/rmo_comprehensive.v` - RMO (list filtering removes all instances)
- `proofs/coq/rmr_simple.v` - RMR (add then remove from list = identity)
- `proofs/isabelle/RMO_Simple.thy` - Polyglot verification (same theorem, different foundation)
- All compile successfully, generate `.vo` certificates

### ❌ Implementation (Unverified)

- `elixir-base/lib/valence_base/rmo.ex` - List filtering (matches Coq conceptually)
- `elixir-base/lib/valence_base/rmr.ex` - List operations (matches Coq conceptually)
- `elixir-base/lib/valence_base/fs_rmr.ex` - Real POSIX mkdir/rmdir (beyond what Coq proves)
- `scripts/demo_fs_rmr.sh` - Bash script demonstrating real directory reversibility (✅ works)

### 📚 Documentation

- `docs/VALENCE_VISION_AND_PROGRESS.adoc` - **READ THIS FIRST** - Honest assessment of gaps and roadmap
- `docs/ARCHITECTURE.adoc` - Zig+BEAM hybrid architecture (documented only, not implemented)
- `docs/blog/2025-11-19-first-maa-proof.adoc` - Contains some overclaims, see vision doc for corrections

## Technology Stack

### Current Implementation
- **Coq** (CIC foundation) - Formal verification
- **Isabelle/HOL** - Cross-validation (different logical foundation)
- **Elixir/BEAM** - Runtime implementation (unverified)
- **Bash** - Demonstration scripts

### Planned Architecture (Documented, Not Built)
- **Zig** - Fast path for simple builtins (5ms cold start target vs bash)
- **BEAM** - Warm daemon for complex operations
- **On-demand verification** - Proof checking when needed
- **Rationale**: BEAM cold start 160ms vs bash 5ms - Zig provides bash-competitive startup

## MAA Framework Primitives

### RMO (Remove-Match-Obliterate)
- **Purpose**: Irreversible deletion with proof of complete removal
- **Status**: Proven for list filtering; real filesystem model needed
- **Use Case**: GDPR "right to be forgotten" with mathematical guarantee

### RMR (Remove-Match-Reverse)
- **Purpose**: Reversible transactions with undo/redo proof
- **Status**: Proven for list operations; needs filesystem model
- **Use Case**: Safe operations with guaranteed rollback

## Critical Gap Identified

**⚠️ Proofs on abstract lists ≠ Proofs on real filesystem operations**

What we have:
```coq
Theorem list_add_remove : forall x l,
  remove x (add x l) = l.
```

What we need:
```coq
Theorem posix_mkdir_rmdir_reversible :
  forall path fs,
    ~ path_exists path fs ->
    rmdir path (mkdir path fs) = fs.
```

**No formal connection exists between Coq proofs and Elixir/Bash code.**

## Next Steps (Roadmap)

### 1. Model Real Filesystem in Coq (2-4 weeks)
- Define `FSNode` with paths, directories, permissions
- Model POSIX `mkdir/rmdir` with error cases:
  - `EEXIST` - path already exists
  - `ENOENT` - parent directory doesn't exist
  - `EACCES` - permission denied
  - `ENOTEMPTY` - directory not empty (for rmdir)

### 2. Prove mkdir/rmdir Reversibility (2-4 weeks)
```coq
Theorem posix_mkdir_rmdir_reversible :
  forall path fs,
    ~ path_exists path fs ->
    parent_exists path fs ->
    has_write_permission path fs ->
    rmdir path (mkdir path fs) = fs.
```

### 3. Extract to Executable Code (4-8 weeks)
**Option A**: Use Coq extraction to OCaml, build FFI to POSIX syscalls
**Option B**: Verify Elixir code matches Coq spec (harder, no automated extraction)

### 4. Close the Verification Gap
- Prove correspondence between abstract model and real implementation
- Build verification pipeline: Spec → Proof → Extraction → Executable

## What We Can Honestly Claim

### ✅ Valid Claims
- Proved list filtering properties in Coq and Isabelle
- Demonstrated real `mkdir/rmdir` reversibility (bash script works)
- Designed bash-competitive architecture (documented)
- Established polyglot verification approach (industry standard: seL4, CompCert)

### ❌ Cannot Claim (Yet)
- **GDPR compliance** - Only proven list filtering, not real deletion pipeline
- **Verified implementation** - Elixir code is unverified
- **Thermodynamic reversibility** - Only algorithmic undo/redo
- **Production ready** - Research phase only

## Important Distinctions

### Algorithmic vs Thermodynamic Reversibility

**Algorithmic Reversibility** (what we have):
- `F⁻¹(F(s)) = s` - operations can be undone
- Information preserved in system state
- Example: `mkdir` then `rmdir` returns to original state

**Thermodynamic Reversibility** (what we DON'T have):
- Energy → 0 (Landauer limit)
- Physical entropy considerations
- Bennett's reversible computing

**We prove the former, not the latter.**

### Polyglot Verification Rationale

Using both Coq (Calculus of Inductive Constructions) and Isabelle (Higher-Order Logic):
- Different logical foundations increase confidence
- Industry standard (seL4 kernel, CompCert compiler)
- Catches foundation-specific errors
- Cross-validation of critical theorems

## Development Guidelines

### For AI Assistants

1. **Be Honest About Gaps**: This is research code. Abstract proofs ≠ real system proofs.
2. **Check VALENCE_VISION_AND_PROGRESS.adoc**: Source of truth for current status
3. **Don't Overclaim**: We cannot claim GDPR compliance or thermodynamic reversibility yet
4. **Verify Before Assuming**: Elixir code may not match Coq proofs
5. **Ask About Ambiguity**: Formal verification requires precision

### Git Workflow
- Main development on GitLab: `git@gitlab.com:non-initiate/rhodinised/vsh.git`
- Work on feature branches (prefix with `claude/` for AI assistant work)
- Commit messages should reference proof/implementation correspondence
- Keep Coq proofs and implementations in sync

### Code Style
- **Coq**: Follow Software Foundations conventions
- **Elixir**: Standard Elixir style guide
- **Zig**: (To be determined when implemented)
- Document correspondence between proofs and code explicitly

### Testing
- Coq proofs must compile and generate `.vo` certificates
- Elixir tests must pass (even though unverified)
- Integration tests must demonstrate real POSIX behavior
- Keep `scripts/demo_fs_rmr.sh` working as regression test

## Key Files Reference

### Proofs
- `proofs/coq/rmo_comprehensive.v` - List filtering theorem
- `proofs/coq/rmr_simple.v` - List add/remove reversibility
- `proofs/isabelle/RMO_Simple.thy` - Cross-validation in Isabelle

### Implementation
- `elixir-base/lib/valence_base/rmo.ex` - RMO implementation (unverified)
- `elixir-base/lib/valence_base/rmr.ex` - RMR implementation (unverified)
- `elixir-base/lib/valence_base/fs_rmr.ex` - Filesystem RMR (unverified)

### Scripts & Demos
- `scripts/demo_fs_rmr.sh` - Working bash demonstration of directory reversibility

### Documentation
- `docs/VALENCE_VISION_AND_PROGRESS.adoc` - **START HERE** - Honest status
- `docs/ARCHITECTURE.adoc` - Zig+BEAM design (not yet built)
- `docs/blog/2025-11-19-first-maa-proof.adoc` - First proof announcement

## Open Questions & Research Directions

**Last Question Asked**: *"What do we need to do to get formal proof of directory creation and reversible delete?"*

**Answer**: See "Next Steps" section above - need to:
1. Model real filesystem in Coq
2. Prove POSIX mkdir/rmdir properties
3. Extract to executable code OR verify implementation matches spec

## Resources

- **Primary Repo**: https://gitlab.com/non-initiate/rhodinised/vsh
- **Coq Documentation**: https://coq.inria.fr/
- **Isabelle Documentation**: https://isabelle.in.tum.de/
- **Software Foundations**: https://softwarefoundations.cis.upenn.edu/ (recommended reading)
- **CompCert** (verified C compiler): https://compcert.org/ (similar verification approach)
- **seL4** (verified kernel): https://sel4.systems/ (gold standard for verified systems)

## Contact & Contribution

*To be added - check GitLab repository for contribution guidelines*

---

**Last Updated**: 2025-11-22
**Version**: 0.2.0 (Comprehensive handover from research phase)
**Status**: Research/Proof-of-Concept - Not Production Ready
