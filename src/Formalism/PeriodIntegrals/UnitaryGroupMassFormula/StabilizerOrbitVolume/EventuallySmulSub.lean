module

public import Mathlib.Topology.Algebra.MulAction
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribSMul.toAddMonoidHom W t)

omit [TopologicalSpace K] in
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z :=
  PI.VolStabS.mem_smulSub t P z

theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) :=
  PI.VolStabS.coe_smulSub t P

theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) :=
  PI.VolStabS.isOpen_smulSub t ht P hP

theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) :=
  PI.VolStabS.isCompact_smulSub t P hP

theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N :=
  PI.VolStabS.eventually_smul_sub S hS s hs N hN

end Abs

end PI.VolStabSW
