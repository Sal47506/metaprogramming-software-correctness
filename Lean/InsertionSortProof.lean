import Mathlib.Data.List.Basic

namespace InsertionSort


def insert (x : Nat) : List Nat → List Nat
| [] => [x]
| y :: ys =>
    if x ≤ y then
      x :: y :: ys
    else
      y :: insert x ys


def insertionSort : List Nat → List Nat
| [] => []
| x :: xs => insert x (insertionSort xs)


def isSorted : List Nat → Prop
| [] => True
| [_] => True
| a :: b :: rest => a ≤ b ∧ isSorted (b :: rest)


/-- inserting into a sorted list preserves sortedness -/
lemma insert_preserves_sorted (xs : List Nat) (x : Nat)
    (h_sorted : isSorted xs) : isSorted (insert x xs) := by
  induction xs with
  | nil =>
      simp [insert, isSorted]
  | cons y ys ih =>
      cases ys with
      | nil =>
          by_cases hxy : x ≤ y
          · simp [insert, hxy, isSorted]
          · simp [insert, hxy, isSorted]
            omega
      | cons z zs =>
          by_cases hxy : x ≤ y
          · simp [insert, hxy, isSorted]
            exact h_sorted
          · have h1 : y ≤ z := h_sorted.left
            have h2 : isSorted (z :: zs) := h_sorted.right
            simp [insert, hxy]
            by_cases hxz : x ≤ z
            · simp [hxz, isSorted]
              constructor
              · omega
              · exact h_sorted.right
            · simp only [hxz, ite_false, isSorted]
              have ih_result := ih h2
              simp only [insert, hxz, ite_false] at ih_result
              exact ⟨h1, ih_result⟩

/-- insertion sort produces a sorted list -/
theorem insertionSort_sorted (xs : List Nat) :
    isSorted (insertionSort xs) := by
  induction xs with
  | nil =>
      simp [insertionSort, isSorted]
  | cons x xs ih =>
      simp [insertionSort]
      exact insert_preserves_sorted (insertionSort xs) x ih

/-- inserting an element produces a permutation -/
lemma insert_is_permutation (xs : List Nat) (x : Nat) :
    (x :: xs).Perm (insert x xs) := by
  induction xs with
  | nil =>
      simp [insert]
  | cons y ys ih =>
      simp only [insert]
      by_cases hxy : x ≤ y
      · simp [hxy]
      · simp [hxy]
        apply List.Perm.trans
        · exact List.Perm.swap y x ys
        · exact List.Perm.cons y ih

/-- insertion sort produces a permutation of the input -/
theorem insertionSort_perm (xs : List Nat) :
    xs.Perm (insertionSort xs) := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      simp [insertionSort]
      apply List.Perm.trans
      · exact List.Perm.cons x ih
      · exact insert_is_permutation (insertionSort xs) x

end InsertionSort


open InsertionSort


#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]


#eval insertionSort [5, 4, 3, 2, 1]

#eval insertionSort []



example : InsertionSort.isSorted (InsertionSort.insertionSort [7, 2, 5, 1, 9]) :=
  InsertionSort.insertionSort_sorted [7, 2, 5, 1, 9]


example : [7, 2, 5, 1, 9].Perm (InsertionSort.insertionSort [7, 2, 5, 1, 9]) :=
  InsertionSort.insertionSort_perm [7, 2, 5, 1, 9]

#check InsertionSort.insertionSort_sorted
#check InsertionSort.insertionSort_perm


namespace MacroVersion

open InsertionSort (insert insertionSort isSorted)



macro "solve_nil_sorted" : tactic =>
  `(tactic| simp [InsertionSort.insert, InsertionSort.isSorted])


macro "solve_single_sorted" h:term : tactic =>
  `(tactic| (
    simp only [InsertionSort.insert];
    split;
    · simp [InsertionSort.isSorted];
      exact $h;
    · simp [InsertionSort.isSorted];
      have : ¬(x ≤ y) := by assumption;
      omega
  ))

-- chain permutations
macro "chain_perms" h1:term "with" h2:term : tactic =>
  `(tactic| exact List.Perm.trans $h1 $h2)

-- swap and cons permutation pattern
macro "swap_and_cons" y:term x:term ys:term ih:term : tactic =>
  `(tactic| (
    have swap := List.Perm.swap $y $x $ys;
    have cons_ih := List.Perm.cons $y $ih;
    exact List.Perm.trans swap cons_ih
  ))



/-- insert preserves sortedness (macro version) -/
lemma insert_sorted_macro (xs : List Nat) (x : Nat)
    (h_sorted : InsertionSort.isSorted xs) : InsertionSort.isSorted (InsertionSort.insert x xs) := by
  induction xs with
  | nil => solve_nil_sorted
  | cons y ys ih =>
      cases ys with
      | nil =>
          simp only [InsertionSort.insert]
          by_cases hxy : x ≤ y
          · simp [hxy, InsertionSort.isSorted]
          · simp [hxy, InsertionSort.isSorted]
            omega
      | cons z zs =>
          by_cases hxy : x ≤ y
          · simp [InsertionSort.insert, hxy, InsertionSort.isSorted]
            exact h_sorted
          · have h1 : y ≤ z := h_sorted.left
            have h2 : InsertionSort.isSorted (z :: zs) := h_sorted.right
            simp [InsertionSort.insert, hxy]
            by_cases hxz : x ≤ z
            · simp [hxz, InsertionSort.isSorted]
              constructor
              · omega
              · exact h_sorted.right
            · simp only [hxz, ite_false, InsertionSort.isSorted]
              have ih_result := ih h2
              simp only [InsertionSort.insert, hxz, ite_false] at ih_result
              exact ⟨h1, ih_result⟩

/-- insertion sort produces sorted list (macro version) -/
theorem sort_sorted_macro (xs : List Nat) :
    InsertionSort.isSorted (InsertionSort.insertionSort xs) := by
  induction xs with
  | nil => simp [InsertionSort.insertionSort, InsertionSort.isSorted]
  | cons x xs ih =>
      simp [InsertionSort.insertionSort]
      exact insert_sorted_macro (InsertionSort.insertionSort xs) x ih


/-- insert preserves permutation (macro version) -/
lemma insert_perm_macro (xs : List Nat) (x : Nat) :
    (x :: xs).Perm (InsertionSort.insert x xs) := by
  induction xs with
  | nil => simp [InsertionSort.insert]
  | cons y ys ih =>
      simp only [InsertionSort.insert]
      by_cases hxy : x ≤ y
      · simp [hxy]
      · simp [hxy]
        have swap := List.Perm.swap y x ys
        have cons_ih := List.Perm.cons y ih
        exact List.Perm.trans swap cons_ih

/-- insertion sort produces permutation (macro version) -/
theorem sort_perm_macro (xs : List Nat) :
    xs.Perm (InsertionSort.insertionSort xs) := by
  induction xs with
  | nil => simp [InsertionSort.insertionSort]
  | cons x xs ih =>
      simp [InsertionSort.insertionSort]
      have cons_perm := List.Perm.cons x ih
      have insert_perm := insert_perm_macro (InsertionSort.insertionSort xs) x
      chain_perms cons_perm with insert_perm

end MacroVersion



example : InsertionSort.isSorted (InsertionSort.insertionSort [9, 3, 7, 1]) :=
  MacroVersion.sort_sorted_macro [9, 3, 7, 1]

example : [9, 3, 7, 1].Perm (InsertionSort.insertionSort [9, 3, 7, 1]) :=
  MacroVersion.sort_perm_macro [9, 3, 7, 1]


#check InsertionSort.insertionSort_sorted    -- original version
#check MacroVersion.sort_sorted_macro        -- macro version
#check InsertionSort.insertionSort_perm      -- original version
#check MacroVersion.sort_perm_macro          -- macro version
