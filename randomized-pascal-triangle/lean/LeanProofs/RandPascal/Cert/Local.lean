import LeanProofs.RandPascal.Cert.Regions

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RandPascal.Cert

noncomputable def localExpect (p a b c d : ℝ) : ℝ :=
  (1-p)^3*out000 a b c d + (1-p)^2*p*out001 a b c d +
  (1-p)^2*p*out010 a b c d + (1-p)*p^2*out011 a b c d +
  (1-p)^2*p*out100 a b c d + (1-p)*p^2*out101 a b c d +
  (1-p)*p^2*out110 a b c d + p^3*out111 a b c d

lemma bernstein_identity (q a b c d : ℝ) :
    base a b c d + localExpect ((29/125 : ℝ)+(96/125 : ℝ)*q) a b c d =
    b0 a b c d*(1-q)^3 + 3*b1 a b c d*q*(1-q)^2 +
    3*b2 a b c d*q^2*(1-q) + b3 a b c d*q^3 := by
  unfold localExpect b0 b1 b2 b3
  ring

theorem local_inequality {p a b c d : ℝ} (hp : (29/125 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (5001/5000 : ℝ)*inputCost a b c d ≤
      localExpect p a b c d+(999/10000 : ℝ)*(a+d-b-c) := by
  let q : ℝ := (125*p-29)/96
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : 0 ≤ 1-q := by dsimp [q]; linarith
  have he : p=(29/125 : ℝ)+(96/125 : ℝ)*q := by dsimp [q]; ring
  obtain ⟨h0,h1,h2,h3⟩ := bernstein_nonneg a b c d ha hb hc hd
  have H : 0 ≤ b0 a b c d*(1-q)^3 + 3*b1 a b c d*q*(1-q)^2 +
      3*b2 a b c d*q^2*(1-q) + b3 a b c d*q^3 := by positivity
  rw [←bernstein_identity,←he] at H
  unfold base at H
  linarith
end RandPascal.Cert
