/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Finite sums of independent gamma variables

The gamma family is closed under sums of independent variables sharing a rate: adding two of them
adds their shapes, which is `TauCeti.gammaMeasure_conv_gammaMeasure`.  This file iterates that
identity over a nonempty finite family, so that a sum of independent gamma variables with a common
positive rate has the gamma law whose shape is the total of the individual shapes.

Splitting a gamma vector into a coordinate and the total of the remaining coordinates is the
elementary use of this closure; combined with the Gamma--Beta change of variables it produces the
coordinate marginals of the Dirichlet distribution.

## Main result

* `TauCeti.hasLaw_sum_gammaMeasure_of_iIndepFun` — a nonempty finite sum of independent gamma
  variables with a common rate is gamma with the summed shape.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {a : ι → ℝ} {r : ℝ}

/-- A nonempty finite sum of independent gamma variables with a common positive rate has the gamma
law whose shape is the sum of the individual shapes. -/
theorem hasLaw_sum_gammaMeasure_of_iIndepFun {s : Finset ι} (hindep : iIndepFun X P) (hr : 0 < r)
    (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i)
    (hlaw : ∀ i, HasLaw (X i) (gammaMeasure (a i) r) P) :
    HasLaw (fun ω ↦ ∑ i ∈ s, X i ω) (gammaMeasure (∑ i ∈ s, a i) r) P := by
  classical
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have key : ∀ t : Finset ι, t.Nonempty → (∀ i ∈ t, 0 < a i) →
      HasLaw (∑ i ∈ t, X i) (gammaMeasure (∑ i ∈ t, a i) r) P := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
        intro _ hat
        have hai : 0 < a i := hat i (Finset.mem_insert_self i t)
        rcases t.eq_empty_or_nonempty with rfl | ht
        · simpa using hlaw i
        · have hat' : ∀ j ∈ t, 0 < a j := fun j hj ↦ hat j (Finset.mem_insert_of_mem hj)
          have htpos : 0 < ∑ j ∈ t, a j := Finset.sum_pos hat' ht
          let _ := isProbabilityMeasure_gammaMeasure hai hr
          let _ := isProbabilityMeasure_gammaMeasure htpos hr
          have hadd := (hindep.indepFun_finsetSum_of_notMem₀
            (fun j ↦ (hlaw j).aemeasurable) hi).symm.hasLaw_add (hlaw i) (ih ht hat')
          rw [gammaMeasure_conv_gammaMeasure hai htpos hr] at hadd
          simpa only [Finset.sum_insert hi] using hadd
  have hfun : (fun ω ↦ ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i :=
    funext fun ω ↦ (Finset.sum_apply ω s X).symm
  rw [hfun]
  exact key s hs ha

end TauCeti
