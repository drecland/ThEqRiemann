import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace RiemannEndDef

structure PermutationBlocsConjugues (n₀ : ℕ) (σ : Equiv.Perm ℕ) : Prop where
  fix_prefix : ∀ n < n₀, σ n = n
  action_paires : ∀ k : ℕ,
    (σ (n₀ + 2 * k) = n₀ + 2 * k ∧ σ (n₀ + 2 * k + 1) = n₀ + 2 * k + 1) ∨
    (σ (n₀ + 2 * k) = n₀ + 2 * k + 1 ∧ σ (n₀ + 2 * k + 1) = n₀ + 2 * k)

noncomputable def sigmaSyntheseFun (γ₀ : ℕ → ℂ) (n₀ : ℕ) (n : ℕ) : ℕ :=
  if n < n₀ then n
  else
    let k := (n - n₀) / 2
    let u := n₀ + 2 * k
    let v := n₀ + 2 * k + 1
    if 0 < (γ₀ u).im then n
    else if (n - n₀) % 2 = 0 then v else u

def zeroSet (Xi : ℂ → ℂ) : Set ℂ := {z : ℂ | Xi z = 0}

noncomputable def multXi (Xi : ℂ → ℂ) (z : ℂ) : ℕ :=
  max 1 (analyticOrderAt Xi z).toNat

def fibreModule (Xi : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z ∈ zeroSet Xi | ‖z‖ = r}

def rayonsSpectraux (Xi : ℂ → ℂ) : Set ℝ :=
  {r : ℝ | (fibreModule Xi r).Nonempty}

def PaliersStricts (Xi : ℂ → ℂ) : Prop :=
  ∀ z w : ℂ, Xi z = 0 → Xi w = 0 → z ≠ w → ‖z‖ = ‖w‖ → w = starRingEnd ℂ z

structure DecompositionFibresSpectrales (Xi : ℂ → ℂ) where
  r : ℕ → ℝ
  j₀ : ℕ
  hj₀ : 2 ≤ j₀
  h_strictMono : StrictMono r
  h_mem : ∀ j : ℕ, r j ∈ rayonsSpectraux Xi
  h_exhaust : ∀ z : ℂ, Xi z = 0 → ∃ j : ℕ, ‖z‖ = r j
  h_real_before : ∀ j < j₀, ∃ x ∈ fibreModule Xi (r j), x.im = 0
  h_non_real_after : ∀ j ≥ j₀, ∀ z ∈ fibreModule Xi (r j), z.im ≠ 0

lemma dichotomie_fibreModule (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (r : ℝ) (hr : r ∈ rayonsSpectraux Xi) :
    (∃! x : ℂ, x ∈ fibreModule Xi r ∧ x.im = 0) ∨
    (∃! z_pos : ℂ, z_pos ∈ fibreModule Xi r ∧ 0 < z_pos.im) := by
  obtain ⟨z, hz_mem, hz_norm⟩ := hr
  have hz_conj_zero : Xi (starRingEnd ℂ z) = 0 := by
    rw [h_symm z, hz_mem, map_zero]
  have hz_conj_fibre : starRingEnd ℂ z ∈ fibreModule Xi r := by
    refine ⟨hz_conj_zero, ?_⟩
    rw [Complex.norm_conj, hz_norm]
  by_cases h_im : z.im = 0
  · left
    use z
    refine ⟨⟨⟨hz_mem, hz_norm⟩, h_im⟩, ?_⟩
    intro w ⟨⟨hw_mem, hw_norm⟩, _⟩
    by_contra h_ne
    have h_eq_conj := h_paliers z w hz_mem hw_mem (Ne.symm h_ne) (hz_norm.trans hw_norm.symm)
    have h_conj_z : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr h_im
    rw [h_conj_z] at h_eq_conj
    exact h_ne h_eq_conj
  · right
    rcases lt_or_gt_of_ne h_im with h_neg | h_pos
    · use starRingEnd ℂ z
      have h_pos_conj : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]; linarith
      refine ⟨⟨hz_conj_fibre, h_pos_conj⟩, ?_⟩
      intro w ⟨⟨hw_mem, hw_norm⟩, hw_pos⟩
      by_contra h_ne
      have h_eq := h_paliers (starRingEnd ℂ z) w hz_conj_zero hw_mem (Ne.symm h_ne)
        (hz_conj_fibre.2.trans hw_norm.symm)
      rw [RingHomCompTriple.comp_apply, RingHom.id_apply] at h_eq
      rw [h_eq] at hw_pos
      linarith
    · use z
      refine ⟨⟨⟨hz_mem, hz_norm⟩, h_pos⟩, ?_⟩
      intro w ⟨⟨hw_mem, hw_norm⟩, hw_pos⟩
      by_contra h_ne
      have h_eq := h_paliers z w hz_mem hw_mem (Ne.symm h_ne) (hz_norm.trans hw_norm.symm)
      rw [h_eq, Complex.conj_im] at hw_pos
      linarith

noncomputable def selectFibre (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) (j : ℕ) : ℂ :=
  if hj : j < D.j₀ then
    Classical.choose (D.h_real_before j hj)
  else
    have h_non_real : ¬ ∃ x ∈ fibreModule Xi (D.r j), x.im = 0 := by
      rintro ⟨x, hx_mem, hx_im⟩
      exact D.h_non_real_after j (not_lt.mp hj) x hx_mem hx_im
    have h_pos : ∃ z_pos : ℂ, z_pos ∈ fibreModule Xi (D.r j) ∧ 0 < z_pos.im := by
      rcases dichotomie_fibreModule Xi h_symm h_paliers
        (D.r j) (D.h_mem j) with ⟨x, hx, _⟩ | ⟨z, hz, _⟩
      · exfalso; exact h_non_real ⟨x, hx.1, hx.2⟩
      · exact ⟨z, hz⟩
    Classical.choose h_pos

noncomputable def gammaChoix (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) (n : ℕ) : ℂ :=
  let n₀ := D.j₀ + 1
  if n = 0 then 0
  else if n < n₀ then
    selectFibre Xi h_symm h_paliers D (n - 1)
  else
    let k := (n - n₀) / 2
    let z_pos := selectFibre Xi h_symm h_paliers D (D.j₀ + k)
    if (n - n₀) % 2 = 0 then z_pos else starRingEnd ℂ z_pos

noncomputable def mChoix (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) (n : ℕ) : ℕ :=
  let n₀ := D.j₀ + 1
  if n < n₀ then
    multXi Xi (gammaChoix Xi h_symm h_paliers D n)
  else
    let k := (n - n₀) / 2
    multXi Xi (selectFibre Xi h_symm h_paliers D (D.j₀ + k))

def FibreNonReelle (Xi : ℂ → ℂ) (rad : ℝ) : Prop :=
  ∀ z ∈ fibreModule Xi rad, z.im ≠ 0




end RiemannEndDef
