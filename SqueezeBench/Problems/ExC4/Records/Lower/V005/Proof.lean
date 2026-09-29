import SqueezeBench.Problems.ExC4.Records.Lower.V005.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V004.Proof

/-! Record V005 for ExC4, lower direction, by baseline claude-opus-5: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V005.lean`. -/

namespace SqueezeBench.ExC4.Lower.V005

open Finset SimpleGraph SqueezeBench SqueezeBench.ExC4

-- Neighbourhood bitmasks of the polarity graph of PG(2,7) on its 57 points.
def mask : ℕ → ℕ
  | 0 => 1134765260439810
  | 1 => 32513
  | 2 => 2287542667837824
  | 3 => 18034192134963472
  | 4 => 36099337629073672
  | 5 => 4648736270582080
  | 6 => 9570441274851616
  | 7 => 72340172838076676
  | 8 => 255
  | 9 => 72624976668147714
  | 10 => 9078122083518466
  | 11 => 4539061041759234
  | 12 => 36312488334073858
  | 13 => 18156244167036930
  | 14 => 2269530520879618
  | 15 => 142989288169013249
  | 16 => 1143771333935232
  | 17 => 1266792032897040
  | 18 => 1407925982069768
  | 19 => 1162218158956608
  | 20 => 1200668979302432
  | 21 => 1691057507140100
  | 22 => 68182605825
  | 23 => 2324368135307328
  | 24 => 18300272078096512
  | 25 => 36047489255605280
  | 26 => 5067099873550352
  | 27 => 9042521872142340
  | 28 => 72198607075541512
  | 29 => 532676609
  | 30 => 4785220637442080
  | 31 => 2815849283979272
  | 32 => 9150170130351232
  | 33 => 18085043211608068
  | 34 => 72075735984115776
  | 35 => 36068383737250320
  | 36 => 1117103813820417
  | 37 => 9017096067498000
  | 38 => 36037601970423872
  | 39 => 2265011200459780
  | 40 => 72066529751474304
  | 41 => 4512400025849864
  | 42 => 18023778735882784
  | 43 => 8727373545473
  | 44 => 18049668814553096
  | 45 => 4521295027374084
  | 46 => 72057671356777488
  | 47 => 2251873096704032
  | 48 => 36591816782647424
  | 49 => 9288745167618624
  | 50 => 4161537
  | 51 => 36170086419054596
  | 52 => 72094978574157856
  | 53 => 18577490331075648
  | 54 => 9029198094049288
  | 55 => 2533584061632528
  | 56 => 4575085331513984
  | _ => 0

-- The 224 edges of that graph, as two coordinate tables.
def ea : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 3
  | 24 => 3
  | 25 => 3
  | 26 => 3
  | 27 => 3
  | 28 => 3
  | 29 => 3
  | 30 => 3
  | 31 => 4
  | 32 => 4
  | 33 => 4
  | 34 => 4
  | 35 => 4
  | 36 => 4
  | 37 => 4
  | 38 => 5
  | 39 => 5
  | 40 => 5
  | 41 => 5
  | 42 => 5
  | 43 => 5
  | 44 => 5
  | 45 => 5
  | 46 => 6
  | 47 => 6
  | 48 => 6
  | 49 => 6
  | 50 => 6
  | 51 => 6
  | 52 => 6
  | 53 => 7
  | 54 => 7
  | 55 => 7
  | 56 => 7
  | 57 => 7
  | 58 => 7
  | 59 => 7
  | 60 => 9
  | 61 => 9
  | 62 => 9
  | 63 => 9
  | 64 => 9
  | 65 => 9
  | 66 => 9
  | 67 => 10
  | 68 => 10
  | 69 => 10
  | 70 => 10
  | 71 => 10
  | 72 => 10
  | 73 => 10
  | 74 => 11
  | 75 => 11
  | 76 => 11
  | 77 => 11
  | 78 => 11
  | 79 => 11
  | 80 => 12
  | 81 => 12
  | 82 => 12
  | 83 => 12
  | 84 => 12
  | 85 => 12
  | 86 => 12
  | 87 => 13
  | 88 => 13
  | 89 => 13
  | 90 => 13
  | 91 => 13
  | 92 => 13
  | 93 => 14
  | 94 => 14
  | 95 => 14
  | 96 => 14
  | 97 => 14
  | 98 => 14
  | 99 => 15
  | 100 => 15
  | 101 => 15
  | 102 => 15
  | 103 => 15
  | 104 => 15
  | 105 => 15
  | 106 => 16
  | 107 => 16
  | 108 => 16
  | 109 => 16
  | 110 => 16
  | 111 => 16
  | 112 => 17
  | 113 => 17
  | 114 => 17
  | 115 => 17
  | 116 => 17
  | 117 => 17
  | 118 => 18
  | 119 => 18
  | 120 => 18
  | 121 => 18
  | 122 => 18
  | 123 => 18
  | 124 => 19
  | 125 => 19
  | 126 => 19
  | 127 => 19
  | 128 => 19
  | 129 => 20
  | 130 => 20
  | 131 => 20
  | 132 => 20
  | 133 => 20
  | 134 => 21
  | 135 => 21
  | 136 => 21
  | 137 => 21
  | 138 => 21
  | 139 => 22
  | 140 => 22
  | 141 => 22
  | 142 => 22
  | 143 => 22
  | 144 => 22
  | 145 => 22
  | 146 => 23
  | 147 => 23
  | 148 => 23
  | 149 => 23
  | 150 => 23
  | 151 => 24
  | 152 => 24
  | 153 => 24
  | 154 => 24
  | 155 => 25
  | 156 => 25
  | 157 => 25
  | 158 => 25
  | 159 => 26
  | 160 => 26
  | 161 => 26
  | 162 => 26
  | 163 => 27
  | 164 => 27
  | 165 => 27
  | 166 => 27
  | 167 => 27
  | 168 => 28
  | 169 => 28
  | 170 => 28
  | 171 => 28
  | 172 => 30
  | 173 => 30
  | 174 => 30
  | 175 => 30
  | 176 => 31
  | 177 => 31
  | 178 => 31
  | 179 => 32
  | 180 => 32
  | 181 => 32
  | 182 => 32
  | 183 => 33
  | 184 => 33
  | 185 => 33
  | 186 => 34
  | 187 => 34
  | 188 => 34
  | 189 => 35
  | 190 => 35
  | 191 => 35
  | 192 => 36
  | 193 => 36
  | 194 => 36
  | 195 => 36
  | 196 => 36
  | 197 => 36
  | 198 => 36
  | 199 => 37
  | 200 => 37
  | 201 => 37
  | 202 => 38
  | 203 => 38
  | 204 => 39
  | 205 => 39
  | 206 => 39
  | 207 => 40
  | 208 => 40
  | 209 => 41
  | 210 => 41
  | 211 => 42
  | 212 => 42
  | 213 => 44
  | 214 => 44
  | 215 => 45
  | 216 => 46
  | 217 => 47
  | 218 => 48
  | 219 => 48
  | 220 => 49
  | 221 => 51
  | 222 => 52
  | 223 => 53
  | _ => 0

def eb : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | 2 => 15
  | 3 => 22
  | 4 => 29
  | 5 => 36
  | 6 => 43
  | 7 => 50
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 7
  | 16 => 8
  | 17 => 21
  | 18 => 27
  | 19 => 33
  | 20 => 39
  | 21 => 45
  | 22 => 51
  | 23 => 4
  | 24 => 8
  | 25 => 18
  | 26 => 28
  | 27 => 31
  | 28 => 41
  | 29 => 44
  | 30 => 54
  | 31 => 8
  | 32 => 17
  | 33 => 26
  | 34 => 35
  | 35 => 37
  | 36 => 46
  | 37 => 55
  | 38 => 6
  | 39 => 8
  | 40 => 20
  | 41 => 25
  | 42 => 30
  | 43 => 42
  | 44 => 47
  | 45 => 52
  | 46 => 8
  | 47 => 19
  | 48 => 23
  | 49 => 34
  | 50 => 38
  | 51 => 49
  | 52 => 53
  | 53 => 8
  | 54 => 16
  | 55 => 24
  | 56 => 32
  | 57 => 40
  | 58 => 48
  | 59 => 56
  | 60 => 14
  | 61 => 21
  | 62 => 28
  | 63 => 35
  | 64 => 42
  | 65 => 49
  | 66 => 56
  | 67 => 11
  | 68 => 18
  | 69 => 25
  | 70 => 32
  | 71 => 39
  | 72 => 46
  | 73 => 53
  | 74 => 17
  | 75 => 24
  | 76 => 31
  | 77 => 38
  | 78 => 45
  | 79 => 52
  | 80 => 13
  | 81 => 20
  | 82 => 27
  | 83 => 34
  | 84 => 41
  | 85 => 48
  | 86 => 55
  | 87 => 19
  | 88 => 26
  | 89 => 33
  | 90 => 40
  | 91 => 47
  | 92 => 54
  | 93 => 16
  | 94 => 23
  | 95 => 30
  | 96 => 37
  | 97 => 44
  | 98 => 51
  | 99 => 50
  | 100 => 51
  | 101 => 52
  | 102 => 53
  | 103 => 54
  | 104 => 55
  | 105 => 56
  | 106 => 20
  | 107 => 26
  | 108 => 32
  | 109 => 38
  | 110 => 44
  | 111 => 50
  | 112 => 21
  | 113 => 24
  | 114 => 34
  | 115 => 37
  | 116 => 47
  | 117 => 50
  | 118 => 19
  | 119 => 28
  | 120 => 30
  | 121 => 39
  | 122 => 48
  | 123 => 50
  | 124 => 23
  | 125 => 35
  | 126 => 40
  | 127 => 45
  | 128 => 50
  | 129 => 27
  | 130 => 31
  | 131 => 42
  | 132 => 46
  | 133 => 50
  | 134 => 25
  | 135 => 33
  | 136 => 41
  | 137 => 49
  | 138 => 50
  | 139 => 29
  | 140 => 30
  | 141 => 31
  | 142 => 32
  | 143 => 33
  | 144 => 34
  | 145 => 35
  | 146 => 24
  | 147 => 29
  | 148 => 41
  | 149 => 46
  | 150 => 51
  | 151 => 29
  | 152 => 42
  | 153 => 48
  | 154 => 54
  | 155 => 29
  | 156 => 40
  | 157 => 44
  | 158 => 55
  | 159 => 29
  | 160 => 39
  | 161 => 49
  | 162 => 52
  | 163 => 28
  | 164 => 29
  | 165 => 37
  | 166 => 45
  | 167 => 53
  | 168 => 29
  | 169 => 38
  | 170 => 47
  | 171 => 56
  | 172 => 33
  | 173 => 37
  | 174 => 48
  | 175 => 52
  | 176 => 40
  | 177 => 49
  | 178 => 51
  | 179 => 35
  | 180 => 41
  | 181 => 47
  | 182 => 53
  | 183 => 38
  | 184 => 46
  | 185 => 54
  | 186 => 39
  | 187 => 44
  | 188 => 56
  | 189 => 42
  | 190 => 45
  | 191 => 55
  | 192 => 43
  | 193 => 44
  | 194 => 45
  | 195 => 46
  | 196 => 47
  | 197 => 48
  | 198 => 49
  | 199 => 40
  | 200 => 43
  | 201 => 53
  | 202 => 43
  | 203 => 55
  | 204 => 42
  | 205 => 43
  | 206 => 51
  | 207 => 43
  | 208 => 56
  | 209 => 43
  | 210 => 52
  | 211 => 43
  | 212 => 54
  | 213 => 45
  | 214 => 54
  | 215 => 52
  | 216 => 56
  | 217 => 51
  | 218 => 49
  | 219 => 55
  | 220 => 53
  | 221 => 55
  | 222 => 56
  | 223 => 54
  | _ => 0

-- Adjacency of the 57-vertex base graph, read off the bitmask table.
def badj (a b : ℕ) : Bool := (mask a).testBit b

theorem badj_symm : ∀ a b : Fin 57, badj a.val b.val = badj b.val a.val := by decide +kernel

theorem badj_irrefl : ∀ a : Fin 57, badj a.val a.val = false := by decide +kernel

-- Two distinct vertices have at most one common neighbour: the bitwise AND of their
-- neighbourhood masks is zero or a single bit. This is `Θ(k²)` machine-integer work,
-- where filtering the common neighbours vertex by vertex would be `Θ(k³)`.
theorem mask_and : ∀ a b : Fin 57, a ≠ b →
    mask a.val &&& mask b.val = 0 ∨
      mask a.val &&& mask b.val = 2 ^ Nat.log2 (mask a.val &&& mask b.val) := by
  decide +kernel

-- Only the `j`-th bit of `2 ^ j` is set.
theorem eq_of_testBit_two_pow {j c : ℕ} (h : (2 ^ j).testBit c = true) : c = j := by
  by_contra hne
  rw [Nat.testBit_two_pow_of_ne (fun hj => hne hj.symm)] at h
  exact Bool.noConfusion h

theorem base_free {a b : Fin 57} {c d : ℕ} (hab : a ≠ b) (h1 : badj a.val c = true)
    (h2 : badj b.val c = true) (h3 : badj a.val d = true) (h4 : badj b.val d = true) : c = d := by
  have hc : (mask a.val &&& mask b.val).testBit c = true := by
    rw [Nat.testBit_and]
    simp only [badj] at h1 h2
    rw [h1, h2]; rfl
  have hd : (mask a.val &&& mask b.val).testBit d = true := by
    rw [Nat.testBit_and]
    simp only [badj] at h3 h4
    rw [h3, h4]; rfl
  rcases mask_and a b hab with h | h
  · rw [h] at hc; simp at hc
  · rw [h] at hc hd
    rw [eq_of_testBit_two_pow hc, eq_of_testBit_two_pow hd]

-- Vertex of index `i` (taken mod `n`, the identity on the indices used below).
def vv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

-- `⌊n/57⌋` disjoint copies of the base graph inside `Fin n`.
def blkGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x.val / 57 = y.val / 57 ∧ badj (x.val % 57) (y.val % 57) = true
  symm := ⟨by
    rintro x y ⟨h, h'⟩
    refine ⟨h.symm, ?_⟩
    rw [badj_symm ⟨y.val % 57, Nat.mod_lt _ (by norm_num)⟩ ⟨x.val % 57, Nat.mod_lt _ (by norm_num)⟩]
    exact h'⟩
  loopless := ⟨by
    rintro x ⟨-, h⟩
    rw [badj_irrefl ⟨x.val % 57, Nat.mod_lt _ (by norm_num)⟩] at h
    exact Bool.noConfusion h⟩

instance (n : ℕ) : DecidableRel (blkGraph n).Adj :=
  fun x y =>
    inferInstanceAs (Decidable (x.val / 57 = y.val / 57 ∧ badj (x.val % 57) (y.val % 57) = true))

theorem blkGraph_free (n : ℕ) : NoTwoCommonNeighbours (blkGraph n) := by
  rintro x y u v hxy huv ⟨bxu, axu⟩ ⟨byu, ayu⟩ ⟨bxv, axv⟩ ⟨byv, ayv⟩
  have hx : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hu : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hab : (⟨x.val % 57, Nat.mod_lt _ (by norm_num)⟩ : Fin 57) ≠ ⟨y.val % 57, Nat.mod_lt _ (by norm_num)⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcd := base_free (a := ⟨x.val % 57, Nat.mod_lt _ (by norm_num)⟩)
    (b := ⟨y.val % 57, Nat.mod_lt _ (by norm_num)⟩) hab axu ayu axv ayv
  omega

theorem edge_lt : ∀ i : Fin 224, ea i.val < eb i.val ∧ eb i.val < 57 := by decide +kernel

theorem edge_inj : ∀ i j : Fin 224, ea i.val = ea j.val → eb i.val = eb j.val → i = j := by
  decide +kernel

theorem edge_adj : ∀ i : Fin 224, badj (ea i.val) (eb i.val) = true := by decide +kernel

theorem edge_lt' {i : ℕ} (hi : i < 224) : ea i < eb i ∧ eb i < 57 := edge_lt ⟨i, hi⟩

theorem blk_card (n : ℕ) (hn : 0 < n) : 224 * (n / 57) ≤ #(blkGraph n).edgeFinset := by
  have key : ∀ p ∈ (Finset.range (n / 57)) ×ˢ (Finset.range 224),
      57 * p.1 + eb p.2 < n ∧ ea p.2 < eb p.2 ∧ eb p.2 < 57 := by
    rintro ⟨b, i⟩ hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hb, hi⟩ := hp
    obtain ⟨h1, h2⟩ := edge_lt' hi
    refine ⟨?_, h1, h2⟩
    omega
  have hval : ∀ p ∈ (Finset.range (n / 57)) ×ˢ (Finset.range 224),
      (vv n hn (57 * p.1 + ea p.2)).val = 57 * p.1 + ea p.2 ∧
      (vv n hn (57 * p.1 + eb p.2)).val = 57 * p.1 + eb p.2 := by
    intro p hp
    obtain ⟨k1, k2, k3⟩ := key p hp
    exact ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
  have hinj : Set.InjOn
      (fun p : ℕ × ℕ => s(vv n hn (57 * p.1 + ea p.2), vv n hn (57 * p.1 + eb p.2)))
      ↑((Finset.range (n / 57)) ×ˢ (Finset.range 224)) := by
    intro p hp q hq h
    have hp' : p ∈ (Finset.range (n / 57)) ×ˢ (Finset.range 224) := by simpa using hp
    have hq' : q ∈ (Finset.range (n / 57)) ×ˢ (Finset.range 224) := by simpa using hq
    obtain ⟨p1, p2⟩ := hval p hp'
    obtain ⟨q1, q2⟩ := hval q hq'
    obtain ⟨-, pa, pb⟩ := key p hp'
    obtain ⟨-, qa, qb⟩ := key q hq'
    have hpi : p.2 < 224 := by simpa using (Finset.mem_product.mp hp').2
    have hqi : q.2 < 224 := by simpa using (Finset.mem_product.mp hq').2
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
  have hsub : ((Finset.range (n / 57)) ×ˢ (Finset.range 224)).image
      (fun p : ℕ × ℕ => s(vv n hn (57 * p.1 + ea p.2), vv n hn (57 * p.1 + eb p.2)))
      ⊆ (blkGraph n).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    obtain ⟨p1, p2⟩ := hval p hp
    obtain ⟨-, pa, pb⟩ := key p hp
    have hpi : p.2 < 224 := by simpa using (Finset.mem_product.mp hp).2
    have hadj := edge_adj ⟨p.2, hpi⟩
    simp only at hadj
    simp only [mem_edgeFinset, mem_edgeSet]
    refine ⟨by rw [p1, p2]; omega, ?_⟩
    have r1 : (vv n hn (57 * p.1 + ea p.2)).val % 57 = ea p.2 := by rw [p1]; omega
    have r2 : (vv n hn (57 * p.1 + eb p.2)).val % 57 = eb p.2 := by rw [p2]; omega
    rw [r1, r2]
    exact hadj
  calc (224 : ℕ) * (n / 57)
      = #(((Finset.range (n / 57)) ×ˢ (Finset.range 224)).image
        (fun p : ℕ × ℕ => s(vv n hn (57 * p.1 + ea p.2), vv n hn (57 * p.1 + eb p.2)))) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
          Finset.card_range, Nat.mul_comm]
    _ ≤ #(blkGraph n).edgeFinset := Finset.card_le_card hsub

theorem blocks_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f blocks := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · exact le_trans (blk_card n hn) (le_f_of_noTwoCommonNeighbours hn (blkGraph_free n))

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V004.valid blocks_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V004.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V004.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 57) (by decide) (by decide +kernel)

end SqueezeBench.ExC4.Lower.V005
