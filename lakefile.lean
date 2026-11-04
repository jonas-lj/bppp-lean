import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io.git" @ "9054989327a7185ff19ef9ff0f119cccea479501"

package «bppp» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target] lean_lib «Bppp» {}
