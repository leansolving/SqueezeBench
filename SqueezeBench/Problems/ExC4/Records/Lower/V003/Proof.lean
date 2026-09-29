import SqueezeBench.Problems.ExC4.Records.Lower.V003.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V002.Proof

/-! Record V003 for ExC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V003.lean`. -/

namespace SqueezeBench.ExC4.Lower.V003

open Finset SimpleGraph SqueezeBench SqueezeBench.ExC4

-- Neighbourhood bitmasks of the polarity graph of PG(2,4) on the 21 points.
def mask : ℕ → ℕ
  | 0 => 2031616
  | 1 => 74272
  | 2 => 100488
  | 3 => 83012
  | 4 => 1048800
  | 5 => 149522
  | 6 => 533528
  | 7 => 295444
  | 8 => 1110016
  | 9 => 267394
  | 10 => 135752
  | 11 => 528420
  | 12 => 1052416
  | 13 => 557378
  | 14 => 262440
  | 15 => 139652
  | 16 => 1048591
  | 17 => 33825
  | 18 => 541313
  | 19 => 272449
  | 20 => 69905
  | _ => 0

def ea : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 2
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 4
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 5
  | 23 => 5
  | 24 => 5
  | 25 => 6
  | 26 => 6
  | 27 => 6
  | 28 => 7
  | 29 => 7
  | 30 => 7
  | 31 => 8
  | 32 => 8
  | 33 => 8
  | 34 => 8
  | 35 => 8
  | 36 => 9
  | 37 => 9
  | 38 => 9
  | 39 => 10
  | 40 => 10
  | 41 => 11
  | 42 => 11
  | 43 => 12
  | 44 => 13
  | 45 => 13
  | 46 => 14
  | 47 => 15
  | 48 => 16
  | 49 => 18
  | _ => 0

def eb : ℕ → ℕ
  | 0 => 16
  | 1 => 17
  | 2 => 18
  | 3 => 19
  | 4 => 20
  | 5 => 5
  | 6 => 9
  | 7 => 13
  | 8 => 16
  | 9 => 3
  | 10 => 7
  | 11 => 11
  | 12 => 15
  | 13 => 16
  | 14 => 6
  | 15 => 10
  | 16 => 14
  | 17 => 16
  | 18 => 5
  | 19 => 6
  | 20 => 7
  | 21 => 20
  | 22 => 11
  | 23 => 14
  | 24 => 17
  | 25 => 10
  | 26 => 13
  | 27 => 19
  | 28 => 9
  | 29 => 15
  | 30 => 18
  | 31 => 12
  | 32 => 13
  | 33 => 14
  | 34 => 15
  | 35 => 20
  | 36 => 10
  | 37 => 12
  | 38 => 18
  | 39 => 12
  | 40 => 17
  | 41 => 12
  | 42 => 19
  | 43 => 20
  | 44 => 15
  | 45 => 19
  | 46 => 18
  | 47 => 17
  | 48 => 20
  | 49 => 19
  | _ => 0

-- Adjacency of the 21-vertex base graph, read off the bitmask table.
def badj (a b : ℕ) : Bool := (mask a).testBit b

theorem badj_symm : ∀ a b : Fin 21, badj a.val b.val = badj b.val a.val := by decide

theorem badj_irrefl : ∀ a : Fin 21, badj a.val a.val = false := by decide

-- Common neighbours of two base vertices.
def cnb (a b : Fin 21) : Finset (Fin 21) :=
  univ.filter (fun u => badj a.val u.val = true ∧ badj b.val u.val = true)

theorem cnb_card : ∀ a b : Fin 21, a ≠ b → #(cnb a b) ≤ 1 := by decide

theorem base_free {a b c d : Fin 21} (hab : a ≠ b) (h1 : badj a.val c.val = true)
    (h2 : badj b.val c.val = true) (h3 : badj a.val d.val = true)
    (h4 : badj b.val d.val = true) : c = d :=
  Finset.card_le_one.mp (cnb_card a b hab) c (by simp [cnb, h1, h2]) d (by simp [cnb, h3, h4])

-- Vertex of index `i` (taken mod `n`, the identity on the indices used below).
def vv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

-- `⌊n/21⌋` disjoint copies of the base graph inside `Fin n`.
def blkGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val / 21 = y.val / 21 ∧ badj (x.val % 21) (y.val % 21) = true
  symm := ⟨by
    rintro x y ⟨h, h'⟩
    refine ⟨h.symm, ?_⟩
    rw [badj_symm ⟨y.val % 21, Nat.mod_lt _ (by norm_num)⟩ ⟨x.val % 21, Nat.mod_lt _ (by norm_num)⟩]
    exact h'⟩
  loopless := ⟨by
    rintro x ⟨-, h⟩
    rw [badj_irrefl ⟨x.val % 21, Nat.mod_lt _ (by norm_num)⟩] at h
    exact Bool.noConfusion h⟩

instance (n : ℕ) : DecidableRel (blkGraph n).Adj :=
  fun x y =>
    inferInstanceAs (Decidable (x.val / 21 = y.val / 21 ∧ badj (x.val % 21) (y.val % 21) = true))

theorem blkGraph_free (n : ℕ) : NoTwoCommonNeighbours (blkGraph n) := by
  rintro x y u v hxy huv ⟨bxu, axu⟩ ⟨byu, ayu⟩ ⟨bxv, axv⟩ ⟨byv, ayv⟩
  have hx : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hu : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hab : (⟨x.val % 21, Nat.mod_lt _ (by norm_num)⟩ : Fin 21) ≠ ⟨y.val % 21, Nat.mod_lt _ (by norm_num)⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcd := base_free (a := ⟨x.val % 21, Nat.mod_lt _ (by norm_num)⟩)
    (b := ⟨y.val % 21, Nat.mod_lt _ (by norm_num)⟩)
    (c := ⟨u.val % 21, Nat.mod_lt _ (by norm_num)⟩)
    (d := ⟨v.val % 21, Nat.mod_lt _ (by norm_num)⟩) hab axu ayu axv ayv
  have := congrArg Fin.val hcd
  simp only at this
  omega

theorem edge_lt : ∀ i : Fin 50, ea i.val < eb i.val ∧ eb i.val < 21 := by decide

theorem edge_inj : ∀ i j : Fin 50, ea i.val = ea j.val → eb i.val = eb j.val → i = j := by decide

theorem edge_adj : ∀ i : Fin 50, badj (ea i.val) (eb i.val) = true := by decide

theorem edge_lt' {i : ℕ} (hi : i < 50) : ea i < eb i ∧ eb i < 21 := edge_lt ⟨i, hi⟩

theorem blk_card (n : ℕ) (hn : 0 < n) : 50 * (n / 21) ≤ #(blkGraph n).edgeFinset := by
  have key : ∀ p ∈ (Finset.range (n / 21)) ×ˢ (Finset.range 50),
      21 * p.1 + eb p.2 < n ∧ ea p.2 < eb p.2 ∧ eb p.2 < 21 := by
    rintro ⟨b, i⟩ hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hb, hi⟩ := hp
    obtain ⟨h1, h2⟩ := edge_lt' hi
    refine ⟨?_, h1, h2⟩
    omega
  have hval : ∀ p ∈ (Finset.range (n / 21)) ×ˢ (Finset.range 50),
      (vv n hn (21 * p.1 + ea p.2)).val = 21 * p.1 + ea p.2 ∧
      (vv n hn (21 * p.1 + eb p.2)).val = 21 * p.1 + eb p.2 := by
    intro p hp
    obtain ⟨k1, k2, k3⟩ := key p hp
    exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
  have hinj : Set.InjOn
      (fun p : ℕ × ℕ => s(vv n hn (21 * p.1 + ea p.2), vv n hn (21 * p.1 + eb p.2)))
      ↑((Finset.range (n / 21)) ×ˢ (Finset.range 50)) := by
    intro p hp q hq h
    have hp' : p ∈ (Finset.range (n / 21)) ×ˢ (Finset.range 50) := by simpa using hp
    have hq' : q ∈ (Finset.range (n / 21)) ×ˢ (Finset.range 50) := by simpa using hq
    obtain ⟨p1, p2⟩ := hval p hp'
    obtain ⟨q1, q2⟩ := hval q hq'
    obtain ⟨-, pa, pb⟩ := key p hp'
    obtain ⟨-, qa, qb⟩ := key q hq'
    have hpi : p.2 < 50 := by simpa using (Finset.mem_product.mp hp').2
    have hqi : q.2 < 50 := by simpa using (Finset.mem_product.mp hq').2
    have hfst : p.1 = q.1 ∧ ea p.2 = ea q.2 ∧ eb p.2 = eb q.2 := by
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := congrArg Fin.val h1
        have a2 := congrArg Fin.val h2
        rw [p1, q1] at a1
        rw [p2, q2] at a2
        omega
      · have a1 := congrArg Fin.val h1
        have a2 := congrArg Fin.val h2
        rw [p1, q2] at a1
        rw [p2, q1] at a2
        omega
    have : p.2 = q.2 := by
      have := edge_inj ⟨p.2, hpi⟩ ⟨q.2, hqi⟩ hfst.2.1 hfst.2.2
      simpa using congrArg Fin.val this
    exact Prod.ext hfst.1 this
  have hsub : ((Finset.range (n / 21)) ×ˢ (Finset.range 50)).image
      (fun p : ℕ × ℕ => s(vv n hn (21 * p.1 + ea p.2), vv n hn (21 * p.1 + eb p.2)))
      ⊆ (blkGraph n).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨p1, p2⟩ := hval p hp
    obtain ⟨-, pa, pb⟩ := key p hp
    have hpi : p.2 < 50 := by simpa using (Finset.mem_product.mp hp).2
    have hadj := edge_adj ⟨p.2, hpi⟩
    simp only at hadj
    simp only [mem_edgeFinset, mem_edgeSet]
    refine ⟨by rw [p1, p2]; omega, ?_⟩
    have r1 : (vv n hn (21 * p.1 + ea p.2)).val % 21 = ea p.2 := by rw [p1]; omega
    have r2 : (vv n hn (21 * p.1 + eb p.2)).val % 21 = eb p.2 := by rw [p2]; omega
    rw [r1, r2]
    exact hadj
  calc 50 * (n / 21)
      = #(((Finset.range (n / 21)) ×ˢ (Finset.range 50)).image
        (fun p : ℕ × ℕ => s(vv n hn (21 * p.1 + ea p.2), vv n hn (21 * p.1 + eb p.2)))) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
          Finset.card_range, Nat.mul_comm]
    _ ≤ #(blkGraph n).edgeFinset := Finset.card_le_card hsub

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f blocks := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (blk_card n hn) (le_f_of_noTwoCommonNeighbours hn (blkGraph_free n))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V002.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V002.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V002.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 21) (by decide) (by decide)

end SqueezeBench.ExC4.Lower.V003
