import mathlib

/-! -/
namespace Meromorphic_On

open Set Complex

lemma meromorphicOn_sub_const {Ω₁ : Set ℂ} {f c : ℂ → ℂ}
    (hf : MeromorphicOn f Ω₁) (hc : MeromorphicOn c Ω₁) :
    MeromorphicOn (fun x => f x - c x) Ω₁ := by
  change MeromorphicOn (f - c) Ω₁
  exact hf.sub hc

lemma meromorphicOn_inv_sub_const {Ω₁ : Set ℂ} {f c : ℂ → ℂ}
    (hsub : MeromorphicOn (fun x => f x - c x) Ω₁) :
    MeromorphicOn (fun x => (f x - c x)⁻¹) Ω₁ := by
  change MeromorphicOn ((fun x : ℂ => f x - c x)⁻¹) Ω₁
  exact hsub.inv

lemma meromorphicOn_deriv_f {Ω₁ : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω₁) :
    MeromorphicOn (deriv f) Ω₁ :=
  hf.deriv

lemma meromorphicOn_pow_id {Ω₁ : Set ℂ} (k : ℕ) :
    MeromorphicOn (fun x : ℂ => x ^ k) Ω₁ := by
  change MeromorphicOn ((id : ℂ → ℂ) ^ k) Ω₁
  exact (MeromorphicOn.id (U := Ω₁)).pow k

lemma meromorphie_integrande {Ω₁ : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω₁) (c : ℂ) (k : ℕ) :
    MeromorphicOn (fun x => x ^ k * deriv f x / (f x - c)) Ω₁ := by
  have hconst : MeromorphicOn (fun _ : ℂ => c) Ω₁ := MeromorphicOn.const c
  have hsub : MeromorphicOn (fun x => f x - c) Ω₁ :=
    meromorphicOn_sub_const hf hconst
  have hinv : MeromorphicOn (fun x => (f x - c)⁻¹) Ω₁ :=
    meromorphicOn_inv_sub_const hsub
  have hderiv : MeromorphicOn (deriv f) Ω₁ :=
    meromorphicOn_deriv_f hf
  have hpow : MeromorphicOn (fun x : ℂ => x ^ k) Ω₁ :=
    meromorphicOn_pow_id (Ω₁ := Ω₁) k
  change MeromorphicOn (((fun x : ℂ => x ^ k) * deriv f) * (fun x : ℂ => (f x - c)⁻¹)) Ω₁
  exact (hpow.mul hderiv).mul hinv




end Meromorphic_On
