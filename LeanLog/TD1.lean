import LeanLog.CustomPrelude

section Excercice1

class Person where
  name : String
  age : Nat

/--
`P(n)` : dans n’importe quel groupe de `n` personnes, tous les gens ont le même âge.
-/
def P (n : ℕ) (_ : 0 < n := by omega) :=
  ∀ {group : List Person}, group.length = n →
    (∀ p₁ p₂, p₁ ∈ group → p₂ ∈ group → p₁.age = p₂.age)

/--
Exercice 1
-/
theorem ex_1 : ∀ n, (hn : n ≥ 1) → P n := by
  intro n hn
  induction n with
  | zero => contradiction
  | succ n IH =>
    intro group hgroup
    let g₁ := group.dropLast -- {p₁, ⋯, pₙ}
    let g₂ := group.tail     -- {p₂, ⋯, pₙ₊₁}

    have hg₁ : g₁.length = n := by
      rw [List.length_dropLast, hgroup]
      rfl

    have hg₂ : g₂.length = n := by
      rw [List.length_tail, hgroup]
      rfl

    -- on ne peut pas appliquer IH directement, car on ne sait pas si `n ≥ 1`!
    -- on peut essayer de le prouver par cas sur `n`
    cases n with
    | zero =>
      rw [List.length_eq_one_iff] at hgroup
      obtain ⟨p, rfl⟩ := hgroup
      intro p₁ p₂ hp₁ hp₂
      rw [List.mem_singleton] at hp₁ hp₂
      subst p₁ p₂
      rfl
    | succ n =>
      intro p₁ p₂ hp₁ hp₂
      -- dans le cas où `p₁ ∈ g₁` et `p₂ ∈ g₂`, on ne peut rien dire
      sorry
  -- ce théorème est faux

end Excercice1

section Excercice2

def isMcNugget (n : ℕ) (_ : 0 < n := by omega) : Prop :=
  ∃ a b c : ℕ, n = a * 6 + b * 9 + c * 20

example : ¬ isMcNugget 43 := by
  rintro ⟨a, b, c, h⟩
  -- `omega` fonctionne directement, mais on détaille un peu...
  -- omega
  have : c ≤ 2 := by omega
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> simp at h
  · have : 3 ∣ 43 := by
      rw [h]
      omega
    contradiction
  · have : 3 ∣ 23 := by
      rw [←h]
      omega
    contradiction
  · have : b = 0 := by omega
    simp [this] at h
    have : 6 ∣ 3 := by
      rw [←h]
      omega
    contradiction

theorem ex_2_2 {n : ℕ} : isMcNugget (44+n) := by
  induction n using Nat.induction₆ with
  | h0 => use 1, 2, 1
  | h1 => use 0, 5, 0
  | h2 => use 1, 0, 2
  | h3 => use 0, 3, 1
  | h4 => use 8, 0, 0
  | h5 => use 0, 1, 2
  | hstep n ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ =>
    simp +arith at *
    obtain ⟨a, b, c, h₄₄⟩ := ih₀
    use a + 1, b, c
    omega

lemma isMcNugget_ge_44 {n : ℕ} (h : 44 ≤ n) : isMcNugget n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  exact ex_2_2

theorem ex_2_3 : {n : ℕ | ∃ h : 0 < n, ¬ isMcNugget n h} =
    {1,2,3,4,5,7,8,10,11,13,14,16,17,19,22,23,25,28,31,34,37,43} := by
  have : {1,2,3,4,5,7,8,10,11,13,14,16,17,19,22,23,25,28,31,34,37,43} = {n : ℕ | n < 44} \
      {0,6,9,12,15,18,20,21,24,26,27,29,30,32,33,35,36,38,39,40,41,42} := by
    ext n
    simp
    omega
  ext n
  rw [this]
  have {h} : ¬ isMcNugget n h → n < 44 := by
    contrapose!
    intro hn
    conv =>
      enter [1]
      rw [(by omega : n = 44 + (n - 44))]
    exact ex_2_2 (n := n - 44)
  simp
  constructor
  · rintro ⟨hn, h⟩
    apply And.intro (not_le.mp <| mt isMcNugget_ge_44 h)
    and_intros <;> (rintro rfl; absurd h)
    · contradiction
    · use 1, 0, 0
    · use 0, 1, 0
    · use 2, 0, 0
    · use 1, 1, 0
    · use 0, 2, 0
    · use 0, 0, 1
    · use 2, 1, 0
    · use 4, 0, 0
    · use 1, 0, 1
    · use 3, 1, 0
    · use 0, 1, 1
    · use 5, 0, 0
    · use 2, 0, 1
    · use 4, 1, 0
    · use 1, 1, 1
    · use 6, 0, 0
    · use 3, 0, 1
    · use 5, 1, 0
    · use 0, 0, 2
    · use 2, 1, 1
    · use 7, 0, 0
  · intro h
    repeat rcases h with ⟨_, h⟩
    exists (by omega)
    have : n ∈ ({1,2,3,4,5,7,8,10,11,13,14,16,17,19,22,23,25,28,31,34,37,43} : Set ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    simp at this
    unfold isMcNugget
    push_neg
    rintro a b c rfl
    repeat' rcases this with this | this <;> omega

end Excercice2

section Excercice3

inductive DyckWord
  | ε : DyckWord
  | wrap (w : DyckWord) : DyckWord
  | concat (w₁ w₂ : DyckWord) : DyckWord

def DyckWord.toString : DyckWord → String
  | DyckWord.ε => ""
  | DyckWord.wrap w => "⟨" ++ DyckWord.toString w ++ "⟩"
  | DyckWord.concat w₁ w₂ => w₁.toString ++ w₂.toString
instance : ToString DyckWord := ⟨DyckWord.toString⟩

def nest (n : ℕ) (w : DyckWord := DyckWord.ε) : DyckWord :=
  match n with
  | 0 => w
  | n+1 => nest n w.wrap

def seq (n : ℕ) (w : DyckWord := DyckWord.ε) : DyckWord :=
  match n with
  | 0 => w
  | n+1 => w.concat (seq n w.wrap)

-- #eval (DyckWord.ε.concat DyckWord.ε.wrap |>.wrap.concat DyckWord.ε.wrap : DyckWord)
-- #eval nest 5
-- #eval seq 5

end Excercice3

section Exercice4

/--
Un arbre binaire strict (ou plein) est un arbre binaire dans lequel chaque nœud interne a
exactement zéro ou deux enfants.
-/
inductive ABS (α : Type)
  | leaf (n : α) : ABS α                          -- ⟨avide, n, avide⟩
  | node (l : ABS α) (n : α) (r : ABS α) : ABS α  -- ⟨l, n, r⟩

def ABS.nodes {α} : ABS α → ℕ
  | ABS.leaf _ => 1
  | ABS.node l _ r => l.nodes + r.nodes + 1

def ABS.leaves {α} : ABS α → ℕ
  | ABS.leaf _ => 1
  | ABS.node l _ r => l.leaves + r.leaves

@[simp]
theorem ABS.leaves_pos {α} {t : ABS α} : 0 < t.leaves := by
  induction t with
  | leaf n => exact Nat.zero_lt_succ 0
  | node l n r ih_l ih_r =>
    rw [ABS.leaves]
    exact Nat.add_pos_left ih_l r.leaves

theorem ex_4_4 (α : Type) (t : ABS α) : t.nodes = 2 * t.leaves - 1 := by
  induction t with
  | leaf n => rw [ABS.nodes, ABS.leaves]
  | node l n r ih_l ih_r =>
    rw [ABS.nodes, ABS.leaves, ih_l, ih_r]
    conv =>
      enter [2,1]
      rw [Nat.left_distrib]
    conv_lhs =>
      rw [Nat.add_assoc]

    rw [Nat.sub_one_add_one]
    · rw [Nat.sub_add_comm, Nat.two_mul]
      rw [Nat.succ_le_iff, Nat.two_mul, Nat.add_pos_iff_pos_or_pos]
      left
      exact ABS.leaves_pos
    · rw [Nat.ne_zero_iff_zero_lt, Nat.two_mul]
      rw [Nat.add_pos_iff_pos_or_pos]
      left
      exact ABS.leaves_pos

end Exercice4

section Excercice5

def somme : List ℕ → ℕ
  | [] => 0
  | n::xs => n + somme xs

def longueur : List ℕ → ℕ
  | [] => 0
  | _::xs => 1 + longueur xs

def maximum : List ℕ → ℕ
  | [] => 0
  | n::xs => max n (maximum xs)

/-
Une façon plus satisfaisante de définir `maximum` est de passer une preuve que la liste
n'est pas vide.
-/
def maximum' : (xs : List ℕ) → (non_empty : xs ≠ []) → ℕ
  | [n], _ => n
  | n::m::xs, _ => max n (maximum' (m::xs) (List.cons_ne_nil m xs))

theorem ex_5_4 : ∀ l : List ℕ, somme l ≤ longueur l * maximum l := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [somme, longueur, maximum, Nat.max_def]
    split_ifs with hmax <;> rw [Nat.right_distrib, Nat.one_mul]
    · apply Nat.add_le_add hmax ih
    · rw [Nat.add_le_add_iff_left]
      rw [Nat.not_le] at hmax
      trans
      · exact ih
      · apply Nat.mul_le_mul
        · rfl
        · exact Nat.le_of_lt hmax

end Excercice5
