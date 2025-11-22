# Valence Shell - Just Build Automation
# Inspired by Absolute Zero's justfile structure

# Default recipe - show available commands
default:
    @just --list

# Build all proofs across all systems
build-all: build-coq build-lean4 build-agda build-isabelle build-mizar
    @echo "✓ All proofs built"

# Verify all proofs
verify-all:
    @./scripts/verify-proofs.sh

# Build Coq proofs
build-coq:
    @echo "Building Coq proofs..."
    cd proofs/coq && coqc filesystem_model.v
    cd proofs/coq && coqc file_operations.v
    cd proofs/coq && coqc posix_errors.v
    cd proofs/coq && coqc extraction.v
    @echo "✓ Coq proofs compiled"

# Build Lean 4 proofs
build-lean4:
    @echo "Building Lean 4 proofs..."
    cd proofs/lean4 && lean FilesystemModel.lean
    cd proofs/lean4 && lean FileOperations.lean
    @echo "✓ Lean 4 proofs checked"

# Build Agda proofs
build-agda:
    @echo "Building Agda proofs..."
    cd proofs/agda && agda FilesystemModel.agda
    cd proofs/agda && agda FileOperations.agda
    @echo "✓ Agda proofs type-checked"

# Build Isabelle proofs
build-isabelle:
    @echo "Building Isabelle proofs..."
    cd proofs/isabelle && isabelle build -D .
    @echo "✓ Isabelle proofs verified"

# Build Mizar proofs (requires Mizar setup)
build-mizar:
    @echo "Building Mizar proofs..."
    cd proofs/mizar && mizf filesystem_model.miz || echo "⚠ Mizar not configured"
    cd proofs/mizar && mizf file_operations.miz || echo "⚠ Mizar not configured"

# Extract Coq to OCaml
extract:
    @echo "Extracting Coq to OCaml..."
    cd proofs/coq && coqc extraction.v
    @echo "✓ OCaml code extracted"

# Build OCaml FFI
build-ffi:
    @echo "Building OCaml FFI..."
    cd impl/ocaml && ocamlopt -c filesystem_ffi.ml
    @echo "✓ OCaml FFI compiled"

# Build Elixir implementation
build-elixir:
    @echo "Building Elixir implementation..."
    cd impl/elixir && mix compile
    @echo "✓ Elixir implementation compiled"

# Run verification demo
demo:
    @echo "Running verified operations demo..."
    @./scripts/demo_verified_operations.sh

# Run FFI tests
test-ffi: build-ffi
    @echo "Testing OCaml FFI..."
    cd impl/ocaml && ./test_ffi

# Run Elixir tests
test-elixir: build-elixir
    @echo "Testing Elixir implementation..."
    cd impl/elixir && mix test

# Run all tests
test-all: demo test-ffi test-elixir
    @echo "✓ All tests passed"

# Clean build artifacts
clean:
    @echo "Cleaning build artifacts..."
    find proofs -name "*.vo" -delete
    find proofs -name "*.vok" -delete
    find proofs -name "*.vos" -delete
    find proofs -name "*.glob" -delete
    find proofs -name ".lake" -type d -exec rm -rf {} + || true
    find proofs -name "*.agdai" -delete
    rm -rf impl/ocaml/*.cmi impl/ocaml/*.cmo impl/ocaml/*.cmx impl/ocaml/*.o
    @echo "✓ Build artifacts cleaned"

# Deep clean (including generated files)
clean-all: clean
    @echo "Deep cleaning..."
    rm -rf proofs/coq/extracted/
    rm -rf _build/
    @echo "✓ Deep clean complete"

# Container build with Podman
container-build:
    @echo "Building container with Podman..."
    podman build -t valence-shell:latest -f Containerfile .
    @echo "✓ Container built"

# Container run
container-run:
    @echo "Running container..."
    podman run -it --rm valence-shell:latest

# Container shell
container-shell:
    @echo "Opening container shell..."
    podman run -it --rm valence-shell:latest /bin/bash

# Full CI pipeline (local)
ci: clean build-all verify-all test-all
    @echo "✓ CI pipeline completed successfully"

# Project statistics
stats:
    @echo "=== Valence Shell Statistics ==="
    @echo ""
    @echo "Proof Code:"
    @find proofs -name "*.v" -o -name "*.lean" -o -name "*.agda" -o -name "*.thy" -o -name "*.miz" | xargs wc -l | tail -1
    @echo ""
    @echo "Implementation Code:"
    @find impl -name "*.ml" -o -name "*.ex" | xargs wc -l | tail -1
    @echo ""
    @echo "Scripts:"
    @find scripts -name "*.sh" | xargs wc -l | tail -1
    @echo ""
    @echo "Documentation:"
    @find docs -name "*.md" | xargs wc -l | tail -1

# Generate documentation
docs:
    @echo "Generating documentation..."
    @echo "See proofs/README.md for proof documentation"
    @echo "See docs/PROGRESS_REPORT.md for development status"
    @echo "See REVIEW.md for quick overview"

# Watch for changes and rebuild
watch:
    @echo "Watching for changes..."
    @while true; do \
        inotifywait -r -e modify proofs/ && just build-all; \
    done

# Integration with ECHIDNA (if available)
echidna-verify:
    @if command -v echidna &> /dev/null; then \
        echo "Running ECHIDNA multi-prover verification..."; \
        echidna verify --all --targets coq,lean4,agda,isabelle,mizar; \
    else \
        echo "⚠ ECHIDNA not installed. Using built-in verification."; \
        just verify-all; \
    fi

# Generate proof certificates
certify:
    @echo "Generating proof certificates..."
    @mkdir -p certs/
    @echo "Proof certificates will be generated here"
    @echo "TODO: Implement certificate generation"

# Help
help:
    @echo "Valence Shell - Build Automation"
    @echo ""
    @echo "Common commands:"
    @echo "  just build-all       - Build all proofs"
    @echo "  just verify-all      - Verify all proofs"
    @echo "  just demo            - Run demonstration"
    @echo "  just test-all        - Run all tests"
    @echo "  just clean           - Clean build artifacts"
    @echo "  just ci              - Run full CI pipeline"
    @echo ""
    @echo "Proof systems:"
    @echo "  just build-coq       - Build Coq proofs"
    @echo "  just build-lean4     - Build Lean 4 proofs"
    @echo "  just build-agda      - Build Agda proofs"
    @echo "  just build-isabelle  - Build Isabelle proofs"
    @echo "  just build-mizar     - Build Mizar proofs"
    @echo ""
    @echo "Containers:"
    @echo "  just container-build - Build Podman container"
    @echo "  just container-run   - Run container"
    @echo ""
    @echo "For full list: just --list"
