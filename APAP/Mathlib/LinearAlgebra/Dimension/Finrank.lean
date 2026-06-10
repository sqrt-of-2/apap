module

public import Mathlib.LinearAlgebra.Dimension.Finrank

public section

@[expose]
noncomputable def Submodule.finrank {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Submodule R M) : ℕ := Module.finrank R s
