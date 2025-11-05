-- Exploring 4.week part of the Algebra (by Prof.Fabien Morel) lecture content in Lean 4
/- `Group Action`, `translation`, `conjugation`, `isotropy subgroup`, `G-invariant`,
`G-equivalent`, `stabilizer`, `orbit`, `orbit decomposition`, `double coset`-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

-- `G-set` (**?not sure?** about the definition is correct...)
structure GSet (G : Type*) [Group G] where
  α : Type*
  inst : MulAction G α

-- From Algebra by Lang: An action of G on S is a homomorphism π : G → Perm(S)
#check MulAction.toPerm

-- the identity of G must correspond to identity permutation of G-set
