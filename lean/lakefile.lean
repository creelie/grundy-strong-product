import Lake
open Lake DSL

package GrundyStrong where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- certificates for "The Grundy domination number is not multiplicative on strong products" -/
@[default_target]
lean_lib GrundyStrong
