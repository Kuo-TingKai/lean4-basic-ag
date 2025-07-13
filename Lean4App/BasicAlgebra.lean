import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

/-!
# 基本代數定理證明

這個文件包含了一些基本的代數定理證明，使用 Lean4 內建類型。
-/

namespace BasicAlgebra

/-!
## 基本定理
-/

-- 定理1: 自然數的基本性質
theorem nat_add_zero (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]

-- 定理2: 自然數乘法的分配律
theorem nat_mul_distrib (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  rw [Nat.mul_add]

-- 定理3: 自然數的結合律
theorem nat_add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]

-- 定理4: 自然數的交換律
theorem nat_add_comm (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]

-- 定理5: 自然數乘法的結合律
theorem nat_mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  rw [Nat.mul_assoc]

/-!
## 集合論的基本概念
-/

-- 定義：集合的包含關係
def set_includes {α : Type*} (A B : Set α) : Prop :=
  ∀ x : α, x ∈ A → x ∈ B

-- 定理6: 集合包含的自反性
theorem set_includes_reflexive {α : Type*} (A : Set α) :
  set_includes A A := by
  unfold set_includes
  intro x hx
  exact hx

-- 定理7: 集合包含的傳遞性
theorem set_includes_transitive {α : Type*} (A B C : Set α) :
  set_includes A B → set_includes B C → set_includes A C := by
  intro hAB hBC
  unfold set_includes
  intro x hx
  have := hAB x hx
  exact hBC x this

/-!
## 函數的基本概念
-/

-- 定義：函數的複合
def function_compose {α β γ : Type*} (f : α → β) (g : β → γ) : α → γ :=
  fun x => g (f x)

-- 定理8: 函數複合的結合律
theorem function_compose_assoc {α β γ δ : Type*} (f : α → β) (g : β → γ) (h : γ → δ) :
  function_compose (function_compose f g) h = function_compose f (function_compose g h) := by
  unfold function_compose
  rfl

/-!
## 邏輯的基本定理
-/

-- 定理9: 雙重否定
theorem double_negation {P : Prop} : ¬¬P ↔ P := by
  constructor
  · intro h
    by_contra h'
    exact h h'
  · intro h h'
    exact h' h

-- 定理10: 德摩根律
theorem demorgan_and {P Q : Prop} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · by_cases hQ : Q
      · exfalso
        exact h ⟨hP, hQ⟩
      · right
        exact hQ
    · left
      exact hP
  · intro h h'
    cases h with
    | inl hP => exact hP h'.1
    | inr hQ => exact hQ h'.2

/-!
## 具體的計算示例
-/

-- 示例：計算斐波那契數列
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

-- 定理11: 斐波那契數列的基本性質
theorem fibonacci_nonnegative (n : ℕ) : fibonacci n ≥ 0 := by
  induction n with
  | zero => simp [fibonacci]
  | succ n ih =>
    cases n with
    | zero => simp [fibonacci]
    | succ n => simp [fibonacci, ih]

-- 示例：計算階乘
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 定理12: 階乘的基本性質
theorem factorial_positive (n : ℕ) : factorial n > 0 := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, ih]

/-!
## 可執行的主函數
-/

def runMain : IO UInt32 := do
  IO.println "=== Lean4 基本代數定理證明 ==="
  IO.println ""
  IO.println "定理1: 自然數加法零元素"
  IO.println s!"3 + 0 = {3 + 0}"
  IO.println ""
  IO.println "定理2: 自然數乘法分配律"
  IO.println s!"2 * (3 + 4) = {2 * (3 + 4)}"
  IO.println s!"2 * 3 + 2 * 4 = {2 * 3 + 2 * 4}"
  IO.println ""
  IO.println "定理11: 斐波那契數列"
  IO.println s!"fibonacci 5 = {fibonacci 5}"
  IO.println s!"fibonacci 6 = {fibonacci 6}"
  IO.println ""
  IO.println "定理12: 階乘"
  IO.println s!"factorial 5 = {factorial 5}"
  IO.println s!"factorial 6 = {factorial 6}"
  IO.println ""
  IO.println "所有定理證明完成！"
  return 0

end BasicAlgebra

def main : IO UInt32 := BasicAlgebra.runMain
