import Lake
open Lake DSL

/-- SHA3-512 from https://github.com/pure-algebra/lean4-hash - a proved, dependency-free
implementation of FIPS 202, used by Merkle/Sha3.lean. -/
require hash from git
  "https://github.com/pure-algebra/lean4-hash" @ "ab7eda433f0390fde7aa240189761540c9744c79"

package merkle where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib Merkle where
  roots := #[`Merkle]

/-- A runnable demonstration: `lake exe merkleDemo`. -/
@[default_target]
lean_exe merkleDemo where
  root := `Main
