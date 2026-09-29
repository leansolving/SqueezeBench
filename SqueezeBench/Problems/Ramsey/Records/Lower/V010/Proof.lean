import SqueezeBench.Problems.Ramsey.Records.Lower.V010.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V009.Proof

/-! Record V010 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V010.lean`. The bound is Spencer's (1975): the symmetric Lovász
Local Lemma applied to the events "the `n`-set `S` is monochromatic" in a random
2-colouring of `K_N`. Everything is finite counting over V006's colourings
`c : Fin N × Fin N → Bool`, with denominators cleared. The local lemma is proved in its
`4pd ≤ 1` form — here `p = 2 / 2^C(n,2)` and `d = C(n,2) · C(N−2, n−2)` — by a strong
induction on the size of the conditioning family: `|A_S ∩ B_Y| · 2^C(n,2) ≤ 4 · |B_Y|` for
every family `Y` of `n`-sets, where `B_Y` is the set of colourings monochromatic on no
member of `Y`. The ingredients are the fibre count `|A_S ∩ B| · 2^C(n,2) ≤ 2 · |B|` for any
`B` determined outside the pairs of `S`, the fact that `B_Y` is such a set when every
member of `Y` shares at most one vertex with `S`, the union bound over the members sharing a
pair, and the count of those members. Positivity of `B_Y` follows by adding one set at a
time, which needs `2^C(n,2) > 4`, i.e. `n ≥ 3`. -/
namespace SqueezeBench.Ramsey.Lower.V010

open SqueezeBench SimpleGraph Finset

variable {N : ℕ}

/-! ## Events -/

-- The colourings monochromatic on `S`.
def bad (S : Finset (Fin N)) : Finset (V006.Col N) := univ.filter (fun c => V006.Mono c S)

-- The colourings monochromatic on no member of `Y`.
def avoid (Y : Finset (Finset (Fin N))) : Finset (V006.Col N) :=
  univ.filter (fun c => ∀ T ∈ Y, ¬ V006.Mono c T)

theorem mem_avoid {Y : Finset (Finset (Fin N))} {c : V006.Col N} :
    c ∈ avoid Y ↔ ∀ T ∈ Y, ¬ V006.Mono c T := by
  simp [avoid]

theorem avoid_anti {Y Y' : Finset (Finset (Fin N))} (h : Y ⊆ Y') : avoid Y' ⊆ avoid Y := by
  intro c hc
  rw [mem_avoid] at hc ⊢
  exact fun T hT => hc T (h hT)

-- Restriction of a colouring to the pairs outside `S`.
def restr (S : Finset (Fin N)) (c : V006.Col N) : ↥((V006.pairs S)ᶜ) → Bool := fun q => c q.1

-- A set of colourings determined by the values outside `S`.
def DetOff (S : Finset (Fin N)) (B : Finset (V006.Col N)) : Prop :=
  ∀ c c', restr S c = restr S c' → (c ∈ B ↔ c' ∈ B)

-- Glue values inside and outside `S` into a colouring.
def glue (S : Finset (Fin N)) (u : ↥(V006.pairs S) → Bool) (v : ↥((V006.pairs S)ᶜ) → Bool) :
    V006.Col N :=
  fun q => if h : q ∈ V006.pairs S then u ⟨q, h⟩ else v ⟨q, Finset.mem_compl.mpr h⟩

theorem restr_glue (S : Finset (Fin N)) (u : ↥(V006.pairs S) → Bool)
    (v : ↥((V006.pairs S)ᶜ) → Bool) : restr S (glue S u v) = v := by
  funext q
  simp only [restr, glue]
  rw [dif_neg (Finset.mem_compl.mp q.2)]

theorem glue_inj (S : Finset (Fin N)) (v : ↥((V006.pairs S)ᶜ) → Bool) :
    Function.Injective (fun u : ↥(V006.pairs S) → Bool => glue S u v) := by
  intro u u' h
  funext q
  have := congrFun h q.1
  simp only [glue, dif_pos q.2] at this
  exact this

/-! ## The fibre count: `P(A_S | B) ≤ p` for `B` determined outside `S` -/

theorem card_bad_inter_le {S : Finset (Fin N)} {B : Finset (V006.Col N)} (hB : DetOff S B) :
    (bad S ∩ B).card * 2 ^ S.card.choose 2 ≤ 2 * B.card := by
  -- each fibre of `bad S ∩ B` over a restriction has at most two elements
  have h1 : (bad S ∩ B).card ≤ 2 * ((bad S ∩ B).image (restr S)).card := by
    refine Finset.card_le_mul_card_image _ _ ?_
    intro v _
    rw [← Fintype.card_bool, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun c : V006.Col N => decide (∀ p ∈ V006.pairs S, c p = true))
      (fun _ _ => Finset.mem_univ _) ?_
    intro c hc c' hc' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_inter] at hc hc'
    have hm : V006.Mono c S := (Finset.mem_filter.mp hc.1.1).2
    have hm' : V006.Mono c' S := (Finset.mem_filter.mp hc'.1.1).2
    have hr : restr S c = restr S c' := hc.2.trans hc'.2.symm
    unfold V006.Mono at hm hm'
    simp only [decide_eq_decide] at h
    funext p
    by_cases hp : p ∈ V006.pairs S
    · rcases hm with hct | hcf
      · rw [hct p hp, h.mp hct p hp]
      · have hnt : ¬ ∀ p ∈ V006.pairs S, c p = true := fun hct => by
          have := hct p hp
          rw [hcf p hp] at this
          exact Bool.noConfusion this
        rcases hm' with hct' | hcf'
        · exact absurd (h.mpr hct') hnt
        · rw [hcf p hp, hcf' p hp]
    · exact congrFun hr ⟨p, Finset.mem_compl.mpr hp⟩
  -- each fibre of `B` over a restriction in its image has `2^C(|S|,2)` elements
  have h2 : 2 ^ S.card.choose 2 * (B.image (restr S)).card ≤ B.card := by
    rw [Finset.card_eq_sum_card_image (restr S) B, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun v hv => ?_)
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hv
    have hcard : Fintype.card (↥(V006.pairs S) → Bool) = 2 ^ S.card.choose 2 := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, V006.card_pairs]
    rw [← hcard, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun u => glue S u (restr S c₀)) ?_ ?_
    · intro u _
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, restr_glue S u (restr S c₀)⟩
      exact (hB _ _ (restr_glue S u (restr S c₀))).mpr hc₀
    · intro u _ u' _ h
      exact glue_inj S (restr S c₀) h
  have h3 : ((bad S ∩ B).image (restr S)).card ≤ (B.image (restr S)).card :=
    Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_right)
  calc (bad S ∩ B).card * 2 ^ S.card.choose 2
      ≤ 2 * ((bad S ∩ B).image (restr S)).card * 2 ^ S.card.choose 2 :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 2 * (B.image (restr S)).card * 2 ^ S.card.choose 2 := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = 2 * (2 ^ S.card.choose 2 * (B.image (restr S)).card) := by ring
    _ ≤ 2 * B.card := Nat.mul_le_mul_left _ h2

/-! ## Independence: sets sharing at most one vertex with `S` -/

theorem mono_congr {S T : Finset (Fin N)} (hTS : (T ∩ S).card < 2) {c c' : V006.Col N}
    (h : restr S c = restr S c') : V006.Mono c T ↔ V006.Mono c' T := by
  have hp : ∀ p ∈ V006.pairs T, c p = c' p := by
    intro p hp
    have hpS : p ∉ V006.pairs S := by
      intro hpS
      rw [V006.mem_pairs] at hp hpS
      have hsub : ({p.1, p.2} : Finset (Fin N)) ⊆ T ∩ S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hp.1, hpS.1⟩
        · exact Finset.mem_inter.mpr ⟨hp.2.1, hpS.2.1⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair (ne_of_lt hp.2.2)] at this
      omega
    exact congrFun h ⟨p, Finset.mem_compl.mpr hpS⟩
  have key : ∀ b : Bool, (∀ p ∈ V006.pairs T, c p = b) ↔ (∀ p ∈ V006.pairs T, c' p = b) :=
    fun b => ⟨fun h1 p hq => by rw [← hp p hq]; exact h1 p hq,
      fun h1 p hq => by rw [hp p hq]; exact h1 p hq⟩
  unfold V006.Mono
  rw [key true, key false]

theorem detOff_avoid {S : Finset (Fin N)} {Y : Finset (Finset (Fin N))}
    (hY : ∀ T ∈ Y, (T ∩ S).card < 2) : DetOff S (avoid Y) := by
  intro c c' h
  rw [mem_avoid, mem_avoid]
  constructor
  · intro hc T hT; rw [← mono_congr (hY T hT) h]; exact hc T hT
  · intro hc T hT; rw [mono_congr (hY T hT) h]; exact hc T hT

/-! ## The dependency count -/

theorem card_dep_le {n : ℕ} {S : Finset (Fin N)} (hS : S.card = n) {Y : Finset (Finset (Fin N))}
    (hY : Y ⊆ powersetCard n univ) :
    (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ n.choose 2 * (N - 2).choose (n - 2) := by
  have hsub : Y.filter (fun T => 2 ≤ (T ∩ S).card) ⊆
      (powersetCard 2 S).biUnion (fun Q => (powersetCard n univ).filter (fun T => Q ⊆ T)) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨Q, hQ, hQ2⟩ := Finset.exists_subset_card_eq hT.2
    rw [Finset.mem_biUnion]
    refine ⟨Q, Finset.mem_powersetCard.mpr ⟨fun x hx => (Finset.mem_inter.mp (hQ hx)).2, hQ2⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hY hT.1, fun x hx => (Finset.mem_inter.mp (hQ hx)).1⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have hc2 : (powersetCard 2 S).card = n.choose 2 := by rw [Finset.card_powersetCard, hS]
  rw [← hc2, ← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ (fun Q hQ => ?_)
  have hQ2 := (Finset.mem_powersetCard.mp hQ).2
  have hcard : (powersetCard (n - 2) (univ \ Q)).card = (N - 2).choose (n - 2) := by
    rw [Finset.card_powersetCard, Finset.card_univ_sdiff, Fintype.card_fin, hQ2]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun T => T \ Q) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hT
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _), ?_⟩
    rw [Finset.card_sdiff_of_subset hT.2, hT.1.2, hQ2]
  · intro T hT T' hT' h
    simp only at h
    have hQT : Q ⊆ T := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
    have hQT' : Q ⊆ T' := (Finset.mem_filter.mp (Finset.mem_coe.mp hT')).2
    rw [← Finset.sdiff_union_of_subset hQT, ← Finset.sdiff_union_of_subset hQT', h]


/-! ## The local lemma: `P(A_S | avoid Y) ≤ 2p` -/

-- Main induction: for `Y ⊆ 𝒫`, `|A_S ∩ B_Y| · 2^C ≤ 4 · |B_Y|`, given `8 d ≤ 2^C` where `d`
-- bounds the number of members of `Y` sharing a pair with `S`.
theorem main_ind {n d : ℕ} (hd : 8 * d ≤ 2 ^ n.choose 2)
    (hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ d) :
    ∀ k, ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ, Y.card ≤ k →
      (bad S ∩ avoid Y).card * 2 ^ n.choose 2 ≤ 4 * (avoid Y).card := by
  intro k
  induction k with
  | zero =>
    intro S hS Y _ hYk
    have hY0 : Y = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hY0
    have h := card_bad_inter_le (S := S) (B := avoid ∅) (fun c c' _ => by simp [mem_avoid])
    rw [(Finset.mem_powersetCard.mp hS).2] at h
    omega
  | succ k ih =>
    intro S hS Y hY hYk
    have hSn := (Finset.mem_powersetCard.mp hS).2
    -- the members of `Y` sharing a pair with `S`, and the others
    have hdet : DetOff S (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))) :=
      detOff_avoid (fun T hT => by have := (Finset.mem_filter.mp hT).2; omega)
    have hA := card_bad_inter_le hdet
    rw [hSn] at hA
    have hY2 : Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card) ⊆ Y := Finset.filter_subset _ _
    have hle1 : (bad S ∩ avoid Y).card ≤
        (bad S ∩ avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card :=
      Finset.card_le_card (Finset.inter_subset_inter_left (avoid_anti hY2))
    -- a colouring avoiding the independent part but not all of `Y` lies in some `bad T`, `T` dependent
    have hcover : avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y ⊆
        (Y.filter (fun T => 2 ≤ (T ∩ S).card)).biUnion
          (fun T => bad T ∩ avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))) := by
      intro c hc
      rw [Finset.mem_sdiff, mem_avoid, mem_avoid] at hc
      obtain ⟨hc2, hcY⟩ := hc
      simp only [not_forall, not_not, exists_prop] at hcY
      obtain ⟨T, hT, hmono⟩ := hcY
      rw [Finset.mem_biUnion]
      refine ⟨T, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hT, ?_⟩
        by_contra hlt
        exact hc2 T (Finset.mem_filter.mpr ⟨hT, hlt⟩) hmono
      · exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmono⟩,
          mem_avoid.mpr hc2⟩
    have hsum : (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card * 2 ^ n.choose 2
        ≤ 4 * d * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := by
      calc (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card * 2 ^ n.choose 2
          ≤ (∑ T ∈ Y.filter (fun T => 2 ≤ (T ∩ S).card),
              (bad T ∩ avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) * 2 ^ n.choose 2 :=
            Nat.mul_le_mul_right _ (le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le)
        _ = ∑ T ∈ Y.filter (fun T => 2 ≤ (T ∩ S).card),
              (bad T ∩ avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card * 2 ^ n.choose 2 :=
            Finset.sum_mul _ _ _
        _ ≤ ∑ T ∈ Y.filter (fun T => 2 ≤ (T ∩ S).card),
              4 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := by
            refine Finset.sum_le_sum (fun T hT => ?_)
            -- `Y` has a dependent member, so its independent part is smaller
            have hY2card : (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)).card ≤ k := by
              have h := Finset.card_filter_add_card_filter_not
                (s := Y) (p := fun T => 2 ≤ (T ∩ S).card)
              have hpos : 0 < (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card :=
                Finset.card_pos.mpr ⟨T, hT⟩
              omega
            exact ih T (hY (Finset.mem_filter.mp hT).1) _ (subset_trans hY2 hY) hY2card
        _ = (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card *
              (4 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ d * (4 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) :=
            Nat.mul_le_mul_right _ (hcount S hS Y hY)
        _ = 4 * d * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := by ring
    have hsplit : (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card =
        (avoid Y).card + (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card := by
      rw [Finset.card_sdiff_of_subset (avoid_anti hY2),
        Nat.add_sub_cancel' (Finset.card_le_card (avoid_anti hY2))]
    have hkey : (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card ≤ 2 * (avoid Y).card := by
      have h2 : 2 ^ n.choose 2 *
          (2 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card) ≤
          2 ^ n.choose 2 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := by
        calc 2 ^ n.choose 2 * (2 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card)
            = 2 * ((avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card)) \ avoid Y).card *
                2 ^ n.choose 2) := by ring
          _ ≤ 2 * (4 * d * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card) :=
              Nat.mul_le_mul_left _ hsum
          _ = (8 * d) * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := by ring
          _ ≤ 2 ^ n.choose 2 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card :=
              Nat.mul_le_mul_right _ hd
      have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
      omega
    calc (bad S ∩ avoid Y).card * 2 ^ n.choose 2
        ≤ (bad S ∩ avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card * 2 ^ n.choose 2 :=
          Nat.mul_le_mul_right _ hle1
      _ ≤ 2 * (avoid (Y.filter (fun T => ¬ 2 ≤ (T ∩ S).card))).card := hA
      _ ≤ 2 * (2 * (avoid Y).card) := Nat.mul_le_mul_left _ hkey
      _ = 4 * (avoid Y).card := by ring

-- Positivity: with `2p < 1`, avoiding every bad event is possible.
theorem avoid_pos {n d : ℕ} (hn : 4 < 2 ^ n.choose 2) (hd : 8 * d ≤ 2 ^ n.choose 2)
    (hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ d) :
    ∀ Y ⊆ powersetCard n (univ : Finset (Fin N)), 0 < (avoid Y).card := by
  intro Y
  induction Y using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.card_pos]
    exact ⟨fun _ => true, mem_avoid.mpr (fun T hT => absurd hT (Finset.notMem_empty _))⟩
  | insert T Y hTY ih =>
    intro hY
    have hY' : Y ⊆ powersetCard n univ := subset_trans (Finset.subset_insert _ _) hY
    have hT : T ∈ powersetCard n univ := hY (Finset.mem_insert_self _ _)
    have hpos := ih hY'
    have hbound := main_ind hd hcount Y.card T hT Y hY' le_rfl
    have heq : avoid (insert T Y) = avoid Y \ (bad T ∩ avoid Y) := by
      ext c
      simp only [mem_avoid, Finset.mem_sdiff, Finset.mem_inter, bad, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
      tauto
    rw [heq, Finset.card_sdiff_of_subset Finset.inter_subset_right]
    have hlt : (bad T ∩ avoid Y).card * 2 ^ n.choose 2 < (avoid Y).card * 2 ^ n.choose 2 :=
      lt_of_le_of_lt hbound (by
        calc 4 * (avoid Y).card = (avoid Y).card * 4 := by ring
          _ < (avoid Y).card * 2 ^ n.choose 2 := Nat.mul_lt_mul_of_pos_left hn hpos)
    have := Nat.lt_of_mul_lt_mul_right hlt
    omega


/-! ## From a good colouring to `¬ Forces` -/

theorem not_forces {n : ℕ} (hn3 : 3 ≤ n)
    (h : 8 * (n.choose 2 * (N - 2).choose (n - 2)) ≤ 2 ^ n.choose 2) : ¬ Forces N n n := by
  intro hF
  have hn4 : 4 < 2 ^ n.choose 2 := by
    have h3 : 3 ≤ n.choose 2 :=
      calc 3 = Nat.choose 3 2 := by decide
        _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn3
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n.choose 2 := Nat.pow_le_pow_right (by norm_num) h3
  have hcount : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), ∀ Y ⊆ powersetCard n univ,
      (Y.filter (fun T => 2 ≤ (T ∩ S).card)).card ≤ n.choose 2 * (N - 2).choose (n - 2) :=
    fun S hS Y hY => card_dep_le (Finset.mem_powersetCard.mp hS).2 hY
  have hpos := avoid_pos hn4 h hcount (powersetCard n univ) (Finset.Subset.refl _)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  rw [mem_avoid] at hc
  rcases hF (V006.graphOf c) with ⟨S, hS⟩ | ⟨T, hT⟩
  · refine hc S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS.card_eq⟩) (Or.inl ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    have hadj := V006.graphOf_adj.mp (hS.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2))
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    exact hadj.2
  · refine hc T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.card_eq⟩) (Or.inr ?_)
    intro p hp
    rw [V006.mem_pairs] at hp
    have hadj := hT.isClique hp.1 hp.2.1 (ne_of_lt hp.2.2)
    rw [compl_adj, V006.graphOf_adj] at hadj
    rw [min_eq_left (le_of_lt hp.2.2), max_eq_right (le_of_lt hp.2.2)] at hadj
    by_contra hcp
    exact hadj.2 ⟨hadj.1, by simpa using hcp⟩

/-! ## The bound -/

-- Any `M` with `8 · C(n,2) · (M−2)^(n−2) ≤ (n−2)! · 2^C(n,2)` gives `f n ≥ M + 1`.
theorem main {n M : ℕ} (hn3 : 3 ≤ n)
    (hM : 8 * n.choose 2 * (M - 2) ^ (n - 2) ≤ (n - 2).factorial * 2 ^ n.choose 2) :
    M + 1 ≤ f n := by
  have hn : nMin ≤ n := by simp [nMin]; omega
  refine le_f hn ?_
  intro N hN
  by_contra hcon
  have hNM : N ≤ M := by omega
  refine not_forces hn3 ?_ hN
  have h1 : (n - 2).factorial * (N - 2).choose (n - 2) ≤ (N - 2) ^ (n - 2) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have h2 : (N - 2) ^ (n - 2) ≤ (M - 2) ^ (n - 2) :=
    Nat.pow_le_pow_left (Nat.sub_le_sub_right hNM 2) _
  have h3 : (n - 2).factorial * (8 * (n.choose 2 * (N - 2).choose (n - 2))) ≤
      (n - 2).factorial * 2 ^ n.choose 2 := by
    calc (n - 2).factorial * (8 * (n.choose 2 * (N - 2).choose (n - 2)))
        = 8 * n.choose 2 * ((n - 2).factorial * (N - 2).choose (n - 2)) := by ring
      _ ≤ 8 * n.choose 2 * (N - 2) ^ (n - 2) := Nat.mul_le_mul_left _ h1
      _ ≤ 8 * n.choose 2 * (M - 2) ^ (n - 2) := Nat.mul_le_mul_left _ h2
      _ ≤ (n - 2).factorial * 2 ^ n.choose 2 := hM
  exact Nat.le_of_mul_le_mul_left h3 (Nat.factorial_pos _)

/-! ## The record -/

theorem bsearch_ok {n K : ℕ} : ∀ fuel lo hi,
    8 * (n * (n - 1) / 2) * (lo - 2) ^ (n - 2) ≤ K →
    8 * (n * (n - 1) / 2) * (bsearch n K fuel lo hi - 2) ^ (n - 2) ≤ K := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h; simpa [bsearch] using h
  | succ fuel ih =>
    intro lo hi h
    rw [bsearch]
    split_ifs with h1 h2
    · exact h
    · exact ih _ _ h2
    · exact ih _ _ h

theorem lll_ok {n : ℕ} (hn3 : 3 ≤ n) :
    8 * n.choose 2 * (lll n - 2) ^ (n - 2) ≤ (n - 2).factorial * 2 ^ n.choose 2 := by
  have h0 : 8 * (n * (n - 1) / 2) * (0 - 2) ^ (n - 2) ≤
      V006.fact (n - 2) * 2 ^ (n * (n - 1) / 2) := by
    rw [Nat.zero_sub, zero_pow (by omega), Nat.mul_zero]
    exact Nat.zero_le _
  have := bsearch_ok (n + 1) 0 (2 ^ n) h0
  change 8 * (n * (n - 1) / 2) * (lll n - 2) ^ (n - 2) ≤
    V006.fact (n - 2) * 2 ^ (n * (n - 1) / 2) at this
  rw [V006.fact_eq, ← Nat.choose_two_right] at this
  exact this

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f v :=
  pin_lowerBoundHolds (fun _ hn => main hn (lll_ok hn))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Ramsey.Lower.V009.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V009.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V009.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Ramsey.nMin) (n₀ := 20) (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V010
