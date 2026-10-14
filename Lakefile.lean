import Lake
open Lake DSL

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
