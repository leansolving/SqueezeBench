import SqueezeBench.Problems.ExC4.Records.Lower.V004.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V003.Proof

/-! Record V004 for ExC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V004.lean`. -/

namespace SqueezeBench.ExC4.Lower.V004

open Finset SimpleGraph SqueezeBench SqueezeBench.ExC4

-- Neighbourhood bitmasks of the polarity graph of PG(2,5) on the 31 points.
def mask : ℕ → ℕ
  | 0 => 2113929216
  | 1 => 50872848
  | 2 => 37884032
  | 3 => 42213632
  | 4 => 35719234
  | 5 => 1106247680
  | 6 => 537989392
  | 7 => 135531012
  | 8 => 269631560
  | 9 => 68690050
  | 10 => 1073772544
  | 11 => 270795920
  | 12 => 545784900
  | 13 => 71370248
  | 14 => 151127298
  | 15 => 1074724864
  | 16 => 138453072
  | 17 => 69255428
  | 18 => 553683080
  | 19 => 276861442
  | 20 => 1073742816
  | 21 => 75630640
  | 22 => 285286436
  | 23 => 136843304
  | 24 => 541343778
  | 25 => 1073741855
  | 26 => 539107841
  | 27 => 8470657
  | 28 => 4720897
  | 29 => 84152385
  | 30 => 34636833
  | _ => 0

def ea : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | 21 => 3
  | 22 => 4
  | 23 => 4
  | 24 => 4
  | 25 => 4
  | 26 => 4
  | 27 => 5
  | 28 => 5
  | 29 => 5
  | 30 => 5
  | 31 => 5
  | 32 => 5
  | 33 => 6
  | 34 => 6
  | 35 => 6
  | 36 => 6
  | 37 => 6
  | 38 => 7
  | 39 => 7
  | 40 => 7
  | 41 => 7
  | 42 => 7
  | 43 => 8
  | 44 => 8
  | 45 => 8
  | 46 => 8
  | 47 => 9
  | 48 => 9
  | 49 => 9
  | 50 => 9
  | 51 => 10
  | 52 => 10
  | 53 => 10
  | 54 => 10
  | 55 => 10
  | 56 => 11
  | 57 => 11
  | 58 => 11
  | 59 => 12
  | 60 => 12
  | 61 => 12
  | 62 => 13
  | 63 => 13
  | 64 => 13
  | 65 => 14
  | 66 => 14
  | 67 => 14
  | 68 => 15
  | 69 => 15
  | 70 => 15
  | 71 => 15
  | 72 => 15
  | 73 => 16
  | 74 => 16
  | 75 => 17
  | 76 => 17
  | 77 => 18
  | 78 => 18
  | 79 => 19
  | 80 => 19
  | 81 => 20
  | 82 => 21
  | 83 => 21
  | 84 => 22
  | 85 => 22
  | 86 => 23
  | 87 => 24
  | 88 => 25
  | 89 => 26
  | _ => 0

def eb : ℕ → ℕ
  | 0 => 25
  | 1 => 26
  | 2 => 27
  | 3 => 28
  | 4 => 29
  | 5 => 30
  | 6 => 4
  | 7 => 9
  | 8 => 14
  | 9 => 19
  | 10 => 24
  | 11 => 25
  | 12 => 7
  | 13 => 12
  | 14 => 17
  | 15 => 22
  | 16 => 25
  | 17 => 8
  | 18 => 13
  | 19 => 18
  | 20 => 23
  | 21 => 25
  | 22 => 6
  | 23 => 11
  | 24 => 16
  | 25 => 21
  | 26 => 25
  | 27 => 20
  | 28 => 21
  | 29 => 22
  | 30 => 23
  | 31 => 24
  | 32 => 30
  | 33 => 8
  | 34 => 12
  | 35 => 16
  | 36 => 20
  | 37 => 29
  | 38 => 9
  | 39 => 11
  | 40 => 18
  | 41 => 20
  | 42 => 27
  | 43 => 14
  | 44 => 17
  | 45 => 20
  | 46 => 28
  | 47 => 13
  | 48 => 19
  | 49 => 20
  | 50 => 26
  | 51 => 11
  | 52 => 12
  | 53 => 13
  | 54 => 14
  | 55 => 30
  | 56 => 18
  | 57 => 21
  | 58 => 28
  | 59 => 19
  | 60 => 23
  | 61 => 29
  | 62 => 16
  | 63 => 22
  | 64 => 26
  | 65 => 17
  | 66 => 24
  | 67 => 27
  | 68 => 16
  | 69 => 17
  | 70 => 18
  | 71 => 19
  | 72 => 30
  | 73 => 22
  | 74 => 27
  | 75 => 21
  | 76 => 26
  | 77 => 24
  | 78 => 29
  | 79 => 23
  | 80 => 28
  | 81 => 30
  | 82 => 23
  | 83 => 26
  | 84 => 24
  | 85 => 28
  | 86 => 27
  | 87 => 29
  | 88 => 30
  | 89 => 29
  | _ => 0

-- Adjacency of the 31-vertex base graph, read off the bitmask table.
def badj (a b : ℕ) : Bool := (mask a).testBit b

theorem badj_symm : ∀ a b : Fin 31, badj a.val b.val = badj b.val a.val := by decide +kernel

theorem badj_irrefl : ∀ a : Fin 31, badj a.val a.val = false := by decide +kernel

-- Common neighbours of two base vertices.
def cnb (a b : Fin 31) : Finset (Fin 31) :=
  univ.filter (fun u => badj a.val u.val = true ∧ badj b.val u.val = true)

theorem cnb_card : ∀ a b : Fin 31, a ≠ b → #(cnb a b) ≤ 1 := by decide +kernel

theorem base_free {a b c d : Fin 31} (hab : a ≠ b) (h1 : badj a.val c.val = true)
    (h2 : badj b.val c.val = true) (h3 : badj a.val d.val = true)
    (h4 : badj b.val d.val = true) : c = d :=
  Finset.card_le_one.mp (cnb_card a b hab) c (by simp [cnb, h1, h2]) d (by simp [cnb, h3, h4])

-- Vertex of index `i` (taken mod `n`, the identity on the indices used below).
def vv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

-- `⌊n/31⌋` disjoint copies of the base graph inside `Fin n`.
def blkGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val / 31 = y.val / 31 ∧ badj (x.val % 31) (y.val % 31) = true
  symm := ⟨by
    rintro x y ⟨h, h'⟩
    refine ⟨h.symm, ?_⟩
    rw [badj_symm ⟨y.val % 31, Nat.mod_lt _ (by norm_num)⟩ ⟨x.val % 31, Nat.mod_lt _ (by norm_num)⟩]
    exact h'⟩
  loopless := ⟨by
    rintro x ⟨-, h⟩
    rw [badj_irrefl ⟨x.val % 31, Nat.mod_lt _ (by norm_num)⟩] at h
    exact Bool.noConfusion h⟩

instance (n : ℕ) : DecidableRel (blkGraph n).Adj :=
  fun x y =>
    inferInstanceAs (Decidable (x.val / 31 = y.val / 31 ∧ badj (x.val % 31) (y.val % 31) = true))

theorem blkGraph_free (n : ℕ) : NoTwoCommonNeighbours (blkGraph n) := by
  rintro x y u v hxy huv ⟨bxu, axu⟩ ⟨byu, ayu⟩ ⟨bxv, axv⟩ ⟨byv, ayv⟩
  have hx : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hu : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hab : (⟨x.val % 31, Nat.mod_lt _ (by norm_num)⟩ : Fin 31) ≠ ⟨y.val % 31, Nat.mod_lt _ (by norm_num)⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcd := base_free (a := ⟨x.val % 31, Nat.mod_lt _ (by norm_num)⟩)
    (b := ⟨y.val % 31, Nat.mod_lt _ (by norm_num)⟩)
    (c := ⟨u.val % 31, Nat.mod_lt _ (by norm_num)⟩)
    (d := ⟨v.val % 31, Nat.mod_lt _ (by norm_num)⟩) hab axu ayu axv ayv
  have := congrArg Fin.val hcd
  simp only at this
  omega

theorem edge_lt : ∀ i : Fin 90, ea i.val < eb i.val ∧ eb i.val < 31 := by decide +kernel

theorem edge_inj : ∀ i j : Fin 90, ea i.val = ea j.val → eb i.val = eb j.val → i = j := by decide +kernel

theorem edge_adj : ∀ i : Fin 90, badj (ea i.val) (eb i.val) = true := by decide +kernel

theorem edge_lt' {i : ℕ} (hi : i < 90) : ea i < eb i ∧ eb i < 31 := edge_lt ⟨i, hi⟩

theorem blk_card (n : ℕ) (hn : 0 < n) : 90 * (n / 31) ≤ #(blkGraph n).edgeFinset := by
  have key : ∀ p ∈ (Finset.range (n / 31)) ×ˢ (Finset.range 90),
      31 * p.1 + eb p.2 < n ∧ ea p.2 < eb p.2 ∧ eb p.2 < 31 := by
    rintro ⟨b, i⟩ hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hb, hi⟩ := hp
    obtain ⟨h1, h2⟩ := edge_lt' hi
    refine ⟨?_, h1, h2⟩
    omega
  have hval : ∀ p ∈ (Finset.range (n / 31)) ×ˢ (Finset.range 90),
      (vv n hn (31 * p.1 + ea p.2)).val = 31 * p.1 + ea p.2 ∧
      (vv n hn (31 * p.1 + eb p.2)).val = 31 * p.1 + eb p.2 := by
    intro p hp
    obtain ⟨k1, k2, k3⟩ := key p hp
    exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
  have hinj : Set.InjOn
      (fun p : ℕ × ℕ => s(vv n hn (31 * p.1 + ea p.2), vv n hn (31 * p.1 + eb p.2)))
      ↑((Finset.range (n / 31)) ×ˢ (Finset.range 90)) := by
    intro p hp q hq h
    have hp' : p ∈ (Finset.range (n / 31)) ×ˢ (Finset.range 90) := by simpa using hp
    have hq' : q ∈ (Finset.range (n / 31)) ×ˢ (Finset.range 90) := by simpa using hq
    obtain ⟨p1, p2⟩ := hval p hp'
    obtain ⟨q1, q2⟩ := hval q hq'
    obtain ⟨-, pa, pb⟩ := key p hp'
    obtain ⟨-, qa, qb⟩ := key q hq'
    have hpi : p.2 < 90 := by simpa using (Finset.mem_product.mp hp').2
    have hqi : q.2 < 90 := by simpa using (Finset.mem_product.mp hq').2
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
  have hsub : ((Finset.range (n / 31)) ×ˢ (Finset.range 90)).image
      (fun p : ℕ × ℕ => s(vv n hn (31 * p.1 + ea p.2), vv n hn (31 * p.1 + eb p.2)))
      ⊆ (blkGraph n).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨p1, p2⟩ := hval p hp
    obtain ⟨-, pa, pb⟩ := key p hp
    have hpi : p.2 < 90 := by simpa using (Finset.mem_product.mp hp).2
    have hadj := edge_adj ⟨p.2, hpi⟩
    simp only at hadj
    simp only [mem_edgeFinset, mem_edgeSet]
    refine ⟨by rw [p1, p2]; omega, ?_⟩
    have r1 : (vv n hn (31 * p.1 + ea p.2)).val % 31 = ea p.2 := by rw [p1]; omega
    have r2 : (vv n hn (31 * p.1 + eb p.2)).val % 31 = eb p.2 := by rw [p2]; omega
    rw [r1, r2]
    exact hadj
  calc 90 * (n / 31)
      = #(((Finset.range (n / 31)) ×ˢ (Finset.range 90)).image
        (fun p : ℕ × ℕ => s(vv n hn (31 * p.1 + ea p.2), vv n hn (31 * p.1 + eb p.2)))) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
          Finset.card_range, Nat.mul_comm]
    _ ≤ #(blkGraph n).edgeFinset := Finset.card_le_card hsub

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f blocks := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (blk_card n hn) (le_f_of_noTwoCommonNeighbours hn (blkGraph_free n))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V003.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V003.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V003.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 31) (by decide) (by decide +kernel)

end SqueezeBench.ExC4.Lower.V004
