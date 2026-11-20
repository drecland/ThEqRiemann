import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.GammaProp
import ThEqRiemann.RiemannProof.XiEntiereProp


/-! -/
namespace LambdaRiemann

open Set Complex RiemannDef GammaRiemann XiEntiereRiemann

lemma lambdaZeros_finite_ball (R : ℝ) :
    (LambdaZeros ∩ Metric.closedBall (0 : ℂ) R).Finite := by
  by_contra hinf
  have hinf' : (LambdaZeros ∩ Metric.closedBall
    (0 : ℂ) R).Infinite := hinf
  have hsub : LambdaZeros ∩ Metric.closedBall
    (0 : ℂ) R ⊆ Metric.closedBall (0 : ℂ) R :=
    Set.inter_subset_right
  obtain ⟨x, _, hacc⟩ :=
    hinf'.exists_accPt_of_subset_isCompact
      (isCompact_closedBall (0 : ℂ) R) hsub
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ, GLambda z = 0 := by
    rw [accPt_iff_frequently] at hacc
    rw [frequently_nhdsWithin_iff]
    refine hacc.mono ?_
    intro z hz
    exact ⟨hz.2.1, hz.1⟩
  have hana : AnalyticOnNhd ℂ GLambda Set.univ :=
    fun z _ => GLambda_differentiable.analyticAt z
  have hzero : Set.EqOn GLambda 0 Set.univ :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ x) hfreq
  have := hzero (Set.mem_univ (Complex.I / 2))
  rw [GLambda_at] at this
  norm_num at this


lemma lambdaZeros_conj {γ : ℂ} (h : γ ∈ LambdaZeros) :
    (starRingEnd ℂ) γ ∈ LambdaZeros := by
  unfold LambdaZeros at *
  simp only [Set.mem_ofPred_eq] at *
  have hc2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have e1 : (1 / 2 : ℂ) + Complex.I * (starRingEnd ℂ) γ
      = (starRingEnd ℂ) (1 - (1 / 2 + Complex.I * γ)) := by
    rw [map_sub, map_one, map_add, hc2, map_mul, Complex.conj_I]
    ring
  rw [e1, xiEntiere_conj, xiEntiere_one_sub, h]
  simp



end LambdaRiemann
