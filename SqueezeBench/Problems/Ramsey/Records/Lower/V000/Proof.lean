import SqueezeBench.Problems.Ramsey.Records.Lower.V000.Def
import SqueezeBench.Problems.Ramsey.Finite

/-!
# Ramsey lower-bound record V000 — validity
-/

namespace SqueezeBench.Ramsey.Lower.V000

open SqueezeBench SimpleGraph

def blockGraph (k N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ (x : ℕ) / k = (y : ℕ) / k
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem card_le_of_isClique {k N : ℕ} (hk : 0 < k) {S : Finset (Fin N)}
    (hS : (blockGraph k N).IsClique ↑S) : S.card ≤ k := by
  have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) % k) ↑S := by
    intro x hx y hy hxy
    by_contra hne
    have hadj : x ≠ y ∧ (x : ℕ) / k = (y : ℕ) / k := hS hx hy hne
    have hmod : (x : ℕ) % k = (y : ℕ) % k := hxy
    refine hne (Fin.ext ?_)
    rw [← Nat.div_add_mod (x : ℕ) k, ← Nat.div_add_mod (y : ℕ) k, hadj.2, hmod]
  have hmaps : ∀ x ∈ S, (x : ℕ) % k ∈ Finset.range k :=
    fun x _ => Finset.mem_range.mpr (Nat.mod_lt _ hk)
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

theorem card_le_of_isClique_compl {k N : ℕ} (hN : N ≤ k * k)
    {T : Finset (Fin N)} (hT : (blockGraph k N)ᶜ.IsClique ↑T) : T.card ≤ k := by
  have hinj : Set.InjOn (fun x : Fin N => (x : ℕ) / k) ↑T := by
    intro x hx y hy hxy
    by_contra hne
    have hadj : x ≠ y ∧ ¬ (blockGraph k N).Adj x y := hT hx hy hne
    exact hadj.2 ⟨hne, hxy⟩
  have hmaps : ∀ x ∈ T, (x : ℕ) / k ∈ Finset.range k := by
    intro x _
    exact Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by omega : (x : ℕ) < k * k))
  simpa using Finset.card_le_card_of_injOn _ hmaps hinj

theorem sq_lt_f {n : ℕ} (hn : nMin ≤ n) : (n - 1) ^ 2 + 1 ≤ f n := by
  refine le_f hn ?_
  intro N hforces
  by_contra hcon
  have hn2 : 2 ≤ n := by simpa using hn
  have hk : 0 < n - 1 := by omega
  have hNk : N ≤ (n - 1) * (n - 1) := by
    have h1 : N ≤ (n - 1) ^ 2 := Nat.lt_succ_iff.mp (Nat.not_le.mp hcon)
    rwa [pow_two] at h1
  rcases hforces (blockGraph (n - 1) N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := card_le_of_isClique hk hS.isClique
    rw [hS.card_eq] at hcard
    omega
  · have hcard := card_le_of_isClique_compl hNk hT.isClique
    rw [hT.card_eq] at hcard
    omega

theorem valid : LowerBoundHolds f record :=
  pin_lowerBoundHolds (fun _ hn => sq_lt_f hn)

end SqueezeBench.Ramsey.Lower.V000
