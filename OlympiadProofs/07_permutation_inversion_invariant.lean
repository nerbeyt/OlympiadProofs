import Mathlib.Tactic

-- General problem: a is a permutation of {0,...,n-1}; Z = a followed by
-- the complement (n-1-a_i). Claim: inv(Z) is always n*(n-1), regardless
-- of the permutation a. For the actual competition problem, n = 10.

def seqZ (n : Nat) (a : Array Nat) : Array Nat :=
  a ++ a.map (fun x => (n - 1) - x)

def inversions (z : Array Nat) : Nat :=
  let m := z.size
  (List.range m).foldl (fun acc i =>
    acc + (List.range m).foldl (fun acc2 j =>
      if i < j && z.getD i 0 > z.getD j 0 then acc2 + 1 else acc2) 0
  ) 0

def invCount (n : Nat) (a : Array Nat) : Nat := inversions (seqZ n a)

-- FULL brute-force verification for small n (n=5, 120 permutations):
-- the invariant inv(Z) = n*(n-1) holds for every single permutation.
theorem invariant_holds_n5 :
    ∀ l ∈ (List.range 5).permutations, invCount 5 l.toArray = 5 * 4 := by
  native_decide

-- Spot check at the actual competition size n=10, on several permutations
-- (identity, reverse, and one shuffled example), consistent with the
-- general formula n*(n-1) = 90:
example : invCount 10 (Array.range 10) = 90 := by native_decide
example : invCount 10 (Array.range 10).reverse = 90 := by native_decide
example : invCount 10 #[3,1,4,0,5,9,2,6,8,7] = 90 := by native_decide
example : invCount 10 #[9,8,7,6,5,4,3,2,1,0] = 90 := by native_decide
example : invCount 10 #[0,2,4,6,8,1,3,5,7,9] = 90 := by native_decide
