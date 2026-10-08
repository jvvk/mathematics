import EnclosingCopy.Enclosing.TangentSimilarity
import EnclosingCopy.Enclosing.EndpointGeometry
import EnclosingCopy.Enclosing.VertexCount

/-!
# Exact finite-copy fitting constraints

At sufficiently small tangent angles, the support maximum on each side comes
from one of that side's two endpoints. The finite fit slack is a quadratic
correction to the limit fit slack.
-/
namespace Enclosing
open Set Filter Topology
variable {m : ℕ} (K : Sides m)

/-- Exact finite fit slack at a side endpoint. -/
noncomputable def tangentFitSlack (q : ℝ) (z : Copy) (i : Fin m) (s : ℝ) : ℝ :=
  z.2.2 * s - Hs K z i + q *
    (z.1 * z.2.2 * s + z.2.2 * dot z.2.1 (sideTangent (K.u i)) +
      z.2.2 ^ 2 * K.h i)

/-- Endpoint test for the physical copy fitting inside the polygon. -/
def TangentFits (q : ℝ) (z : Copy) : Prop :=
  ∀ i, 0 ≤ tangentFitSlack K q z i (K.a i) ∧
    0 ≤ tangentFitSlack K q z i (K.b i)

lemma tangentSimilarity_dot (q : ℝ) (z : Copy) (x u : ℝ × ℝ) :
    dot (tangentSimilarity q z x) u =
      ((1 + q * z.1) * (dot x u - q * z.2.2 * dot x (sideTangent u)) +
        q * (dot z.2.1 u - q * z.2.2 * dot z.2.1 (sideTangent u))) /
          (1 + (q * z.2.2) ^ 2) := by
  simp [tangentSimilarity, tangentRotate, sideTangent, dot]; ring

lemma tangent_endpoint_fits {q : ℝ} (hq : 0 < q) (z : Copy) (hG : GoodSides K)
    (i : Fin m) (s : ℝ) :
    dot (tangentSimilarity q z (sideChart (K.u i) (K.h i) (s, 0))) (K.u i) ≤ K.h i ↔
      0 ≤ tangentFitSlack K q z i s := by
  have he := sideCoords_chart (K.u i) (hG.unit i) (K.h i) (s, 0)
  have hu : dot (sideChart (K.u i) (K.h i) (s, 0)) (K.u i) = K.h i := by
    have h := congrArg Prod.snd he
    dsimp [sideCoords] at h; linarith
  have ht : dot (sideChart (K.u i) (K.h i) (s, 0)) (sideTangent (K.u i)) = s :=
    congrArg Prod.fst he
  rw [tangentSimilarity_dot, hu, ht, div_le_iff₀ (by positivity)]
  have hmul : 0 ≤ q * tangentFitSlack K q z i s ↔
      0 ≤ tangentFitSlack K q z i s := (mul_nonneg_iff_of_pos_left hq)
  rw [← hmul]
  unfold tangentFitSlack Hs
  constructor <;> intro h <;> nlinarith

/-- Linear endpoint excess controls the support maximum for small tangent angles. -/
lemma tangent_support_le (i : Fin m) (C : ℝ) (_hC : 0 ≤ C)
    (henlarge : ∀ d ≥ 0, physicalSideStrip K i d ⊆
      sideWindow K i (K.a i - C * d) (K.b i + C * d) d)
    (hG : GoodSides K) {t : ℝ} (ht : |t| * C ≤ 1)
    {x : ℝ × ℝ} (hx : x ∈ polygonRegion K) :
    dot x (K.u i) - t * dot x (sideTangent (K.u i)) ≤
      K.h i - min (t * K.a i) (t * K.b i) := by
  let d := K.h i - dot x (K.u i)
  have hd : 0 ≤ d := sub_nonneg.mpr (hx i)
  obtain ⟨p, hp, hpx⟩ := henlarge d hd ⟨hx, hd, le_rfl⟩
  have he := sideCoords_chart (K.u i) (hG.unit i) (K.h i) p
  rw [hpx] at he
  have hs : dot x (sideTangent (K.u i)) = p.1 := congrArg Prod.fst he
  rw [hs]
  rcases le_total 0 t with ht0 | ht0
  · rw [min_eq_left (mul_le_mul_of_nonneg_left (K.hab i).le ht0)]
    rw [abs_of_nonneg ht0] at ht
    have h1 := mul_le_mul_of_nonneg_left hp.1.1 ht0
    have h2 := mul_le_mul_of_nonneg_right ht hd
    dsimp [d] at h1 h2
    nlinarith
  · rw [min_eq_right (mul_le_mul_of_nonpos_left (K.hab i).le ht0)]
    rw [abs_of_nonpos ht0] at ht
    have h1 := mul_le_mul_of_nonpos_left hp.1.2 ht0
    have h2 := mul_le_mul_of_nonneg_right ht hd
    dsimp [d] at h1 h2
    nlinarith

variable [NeZero m] {v : Fin m → ℝ × ℝ}

/-- Near zero angle, the endpoint test is exactly physical set containment. -/
theorem exists_tangent_fit_radius (hm : 3 ≤ m) (hv : ConvexPos v)
    (harea : area v = 1) :
    let K := sidesOf v hm hv harea
    ∃ r > 0, ∀ q > 0, ∀ z : Copy, 0 < 1 + q * z.1 → |q * z.2.2| ≤ r →
      (tangentCopyRegion K q z ⊆ polygonRegion K ↔ TangentFits K q z) := by
  intro K
  choose C hC hbound using fun i => exists_physicalSideStrip_enlargement hm hv harea i
  let B := ∑ i, C i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hC i
  let r := 1 / (B + 1)
  have hr : 0 < r := one_div_pos.mpr (by linarith)
  refine ⟨r, hr, ?_⟩
  intro q hq z hz hzr
  have hsmall (i : Fin m) : |q * z.2.2| * C i ≤ 1 := by
    have hci : C i ≤ B := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i)
    have he : r * (B + 1) = 1 := by dsimp [r]; field_simp
    have h1 := mul_le_mul_of_nonneg_right hzr (hC i)
    have h2 := mul_le_mul_of_nonneg_left hci hr.le
    nlinarith
  have hG := goodSides_of_convex hm hv harea
  constructor
  · intro hfit i
    have ha : sideChart (K.u i) (K.h i) (K.a i, 0) ∈ polygonRegion K := by
      rw [show sideChart (K.u i) (K.h i) (K.a i, 0) = v i from sideChart_start hm hv i]
      exact fun j => vertex_support_le hv j i
    have hb : sideChart (K.u i) (K.h i) (K.b i, 0) ∈ polygonRegion K := by
      rw [show sideChart (K.u i) (K.h i) (K.b i, 0) = v (i + 1) from
        sideChart_end hm hv i]
      exact fun j => vertex_support_le hv j (i + 1)
    exact ⟨(tangent_endpoint_fits K hq z hG i _).mp
      (hfit ⟨_, ha, rfl⟩ i), (tangent_endpoint_fits K hq z hG i _).mp
      (hfit ⟨_, hb, rfl⟩ i)⟩
  · intro hfit x hx
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    have hsup := tangent_support_le K i (C i) (hC i) (hbound i) hG (hsmall i) hy
    have h1 := (tangent_endpoint_fits K hq z hG i (K.a i)).mpr (hfit i).1
    have h2 := (tangent_endpoint_fits K hq z hG i (K.b i)).mpr (hfit i).2
    have hcoords (s : ℝ) :
        dot (sideChart (K.u i) (K.h i) (s, 0)) (K.u i) = K.h i ∧
        dot (sideChart (K.u i) (K.h i) (s, 0)) (sideTangent (K.u i)) = s := by
      have he := sideCoords_chart (K.u i) (hG.unit i) (K.h i) (s, 0)
      constructor
      · have h := congrArg Prod.snd he; dsimp [sideCoords] at h; linarith
      · exact congrArg Prod.fst he
    rw [tangentSimilarity_dot, (hcoords _).1, (hcoords _).2,
      div_le_iff₀ (by positivity)] at h1 h2
    rw [tangentSimilarity_dot, div_le_iff₀ (by positivity)]
    have hb := mul_le_mul_of_nonneg_left hsup hz.le
    rcases le_total (q * z.2.2 * K.a i) (q * z.2.2 * K.b i) with h | h
    · rw [min_eq_left h] at hb; linarith
    · rw [min_eq_right h] at hb; linarith

end Enclosing
