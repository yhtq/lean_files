import Mathlib.Tactic

def match_fin (s: Fin 5) : Fin 6:=
  match s with
  | ⟨n, _⟩ => ⟨n + 1, by omega⟩

example (m n : ℕ) (h1: m < 5) (h2: n < 5) (eq: m = n) : match_fin ⟨m, h1⟩ = match_fin ⟨n, h2⟩ := by
  unfold match_fin


variable {A: Type*} [DecidableEq A] [PartialOrder A]  [DecidableRel fun (x x_1 : A) => x < x_1]

def quicksort (l: List A) : List A :=
  match l with
  | [] => []
  | x::xs =>
    let lp := List.partition (· <  x) xs
    (quicksort $ Prod.fst lp) ++ [x] ++ (quicksort $ Prod.snd lp)
termination_by List.length l
decreasing_by
  all_goals (simp_wf; apply Nat.lt_add_one_of_le; apply List.length_filter_le)
#eval quicksort [1, 2, 3, 0, 5, 6, 3]
