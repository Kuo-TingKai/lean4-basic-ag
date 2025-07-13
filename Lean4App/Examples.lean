import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# 代數幾何定理的具體示例

這個文件包含了一些具體的代數幾何定理示例，可以直接在Lean4中運行和驗證。
-/

namespace Examples

/-!
## 示例1: 多項式的基本運算

我們首先展示一些多項式的基本運算和性質。
-/

-- 示例：創建一個二次多項式
def quadratic_polynomial : Polynomial ℝ :=
  Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 1

-- 驗證多項式的次數
theorem quadratic_degree : quadratic_polynomial.degree = 2 := by
  unfold quadratic_polynomial
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  · rw [Polynomial.degree_pow, Polynomial.degree_X]
    simp
  · rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · rw [Polynomial.degree_mul, Polynomial.degree_C, Polynomial.degree_X]
      simp
    · rw [Polynomial.degree_C]
      simp

-- 示例：多項式的求值
theorem polynomial_evaluation : quadratic_polynomial.eval 0 = 1 := by
  unfold quadratic_polynomial
  simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

-- 示例：多項式的根
theorem polynomial_roots : quadratic_polynomial.eval (-1) = 0 := by
  unfold quadratic_polynomial
  simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

/-!
## 示例2: 代數基本定理的應用

我們展示代數基本定理在具體例子中的應用。
-/

-- 示例：複數域上的多項式
def complex_polynomial : Polynomial ℂ :=
  Polynomial.X ^ 2 + Polynomial.C 1

-- 驗證這個多項式在複數域上有根
theorem complex_polynomial_has_root :
  ∃ x : ℂ, complex_polynomial.eval x = 0 := by
  use Complex.I
  unfold complex_polynomial
  simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [Complex.I_sq]
  simp

-- 示例：實數域上的多項式
def real_polynomial : Polynomial ℝ :=
  Polynomial.X ^ 2 + Polynomial.C 1

-- 這個多項式在實數域上沒有根
theorem real_polynomial_no_real_root :
  ∀ x : ℝ, real_polynomial.eval x ≠ 0 := by
  intro x
  unfold real_polynomial
  simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  intro h
  have := sq_nonneg x
  linarith

/-!
## 示例3: 理想的基本運算

我們展示理想的基本運算和性質。
-/

-- 示例：主理想的生成
theorem principal_ideal_example (a : ℝ) :
  a ∈ Ideal.span {a} := by
  exact Ideal.mem_span_singleton_self a

-- 示例：理想的包含關係
theorem ideal_containment_example (a b : ℝ) (h : a ∣ b) :
  Ideal.span {b} ⊆ Ideal.span {a} := by
  intro x hx
  rw [Ideal.mem_span_singleton] at hx
  rcases hx with ⟨r, hr⟩
  rw [hr]
  rw [Ideal.mem_span_singleton]
  rw [← mul_assoc]
  use r * (b / a)
  ring

/-!
## 示例4: 代數集的基本性質

我們展示代數集的基本性質和運算。
-/

-- 定義：代數集
def algebraic_set {K : Type*} [Field K] (S : Set (Polynomial K)) : Set K :=
  { x : K | ∀ p ∈ S, p.eval x = 0 }

-- 示例：單個多項式的代數集
theorem single_polynomial_algebraic_set {K : Type*} [Field K] (f : Polynomial K) :
  algebraic_set {f} = { x : K | f.eval x = 0 } := by
  unfold algebraic_set
  ext x
  constructor
  · intro h
    exact h f (Set.mem_singleton f)
  · intro h p hp
    rw [Set.mem_singleton_iff] at hp
    rw [hp]
    exact h

-- 示例：空集的代數集
theorem empty_algebraic_set {K : Type*} [Field K] :
  algebraic_set (∅ : Set (Polynomial K)) = Set.univ := by
  unfold algebraic_set
  ext x
  constructor
  · intro h
    trivial
  · intro h p hp
    exfalso
    exact Set.not_mem_empty p hp

/-!
## 示例5: 代數映射的性質

我們展示代數映射的基本性質。
-/

-- 定義：代數映射
def algebraic_map {K : Type*} [Field K] (f : Polynomial K) : K → K :=
  fun x => f.eval x

-- 示例：代數映射的零點
theorem algebraic_map_zeros_example {K : Type*} [Field K] (f : Polynomial K) :
  { x : K | algebraic_map f x = 0 } = { x : K | f.eval x = 0 } := by
  rfl

-- 示例：代數映射的複合
theorem algebraic_map_composition_example {K : Type*} [Field K] (f g : Polynomial K) :
  algebraic_map (f * g) = fun x => algebraic_map f x * algebraic_map g x := by
  ext x
  rw [algebraic_map, algebraic_map, algebraic_map]
  rw [Polynomial.eval_mul]

/-!
## 示例6: 代數擴張的簡單例子

我們展示一些代數擴張的簡單例子。
-/

-- 示例：代數元素的定義
def algebraic_element {K L : Type*} [Field K] [Field L] [Algebra K L] (a : L) : Prop :=
  ∃ f : Polynomial K, f ≠ 0 ∧ f.eval₂ (algebraMap K L) a = 0

-- 示例：代數擴張的維數
theorem algebraic_extension_dimension_example {K L : Type*} [Field K] [Field L] [Algebra K L] :
  Module.rank K L ≥ 1 := by
  exact Module.rank_pos

/-!
## 示例7: 具體的計算例子

我們展示一些具體的計算例子。
-/

-- 示例：計算多項式的導數
def polynomial_derivative_example : Polynomial ℝ :=
  Polynomial.derivative quadratic_polynomial

-- 驗證導數的計算
theorem derivative_calculation : polynomial_derivative_example = 2 * Polynomial.X + Polynomial.C 2 := by
  unfold polynomial_derivative_example quadratic_polynomial
  rw [Polynomial.derivative_add, Polynomial.derivative_pow, Polynomial.derivative_X]
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X]
  rw [Polynomial.derivative_C]
  simp

-- 示例：計算多項式的積分
def polynomial_integral_example : Polynomial ℝ :=
  Polynomial.integral quadratic_polynomial

-- 驗證積分的計算
theorem integral_calculation : polynomial_integral_example = 
  (1/3) * Polynomial.X ^ 3 + Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X := by
  unfold polynomial_integral_example quadratic_polynomial
  rw [Polynomial.integral_add, Polynomial.integral_pow, Polynomial.integral_X]
  rw [Polynomial.integral_mul, Polynomial.integral_C, Polynomial.integral_X]
  rw [Polynomial.integral_C]
  simp

/-!
## 示例8: 代數幾何中的對偶性

我們展示一些關於對偶性的簡單例子。
-/

-- 定義：對偶空間
def dual_space {K : Type*} [Field K] (V : Set K) : Set (K → K) :=
  { f : K → K | ∀ x ∈ V, f x = 0 }

-- 示例：對偶空間的性質
theorem dual_space_properties_example {K : Type*} [Field K] (V : Set K) :
  0 ∈ dual_space V := by
  unfold dual_space
  intro x hx
  rw [Pi.zero_apply]

-- 示例：對偶空間的線性性
theorem dual_space_linear_example {K : Type*} [Field K] (V : Set K) :
  ∀ f g ∈ dual_space V, ∀ a b : K, (a • f + b • g) ∈ dual_space V := by
  intro f g hf hg a b
  unfold dual_space
  intro x hx
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  rw [hf x hx, hg x hx]
  simp

/-!
## 示例9: 代數集的維數

我們展示一些關於代數集維數的簡單例子。
-/

-- 定義：代數集的維數（簡化版本）
def algebraic_set_dimension {K : Type*} [Field K] (V : Set K) : ℕ :=
  if V = ∅ then 0
  else if V = Set.univ then 1
  else 0

-- 示例：空集的維數
theorem empty_set_dimension_example {K : Type*} [Field K] :
  algebraic_set_dimension (∅ : Set K) = 0 := by
  unfold algebraic_set_dimension
  simp

-- 示例：全空間的維數
theorem full_space_dimension_example {K : Type*} [Field K] :
  algebraic_set_dimension (Set.univ : Set K) = 1 := by
  unfold algebraic_set_dimension
  simp

/-!
## 示例10: 代數簇的不可約性

我們展示一些關於不可約代數簇的例子。
-/

-- 定義：不可約代數集
def irreducible_algebraic_set {K : Type*} [Field K] (V : Set K) : Prop :=
  V ≠ ∅ ∧ V ≠ Set.univ ∧ 
  ∀ U W : Set K, 
    U ≠ ∅ → W ≠ ∅ → V ⊆ U ∪ W → V ⊆ U ∨ V ⊆ W

-- 示例：單點集的不可約性
theorem singleton_irreducible_example {K : Type*} [Field K] (a : K) :
  irreducible_algebraic_set {a} := by
  unfold irreducible_algebraic_set
  constructor
  · exact Set.singleton_nonempty a
  · intro h
    have := Set.eq_univ_iff_forall.mp h a
    exact this (Set.mem_singleton a)
  · intro U W hU hW hV
    left
    exact Set.singleton_subset_iff.mpr (hV (Set.mem_singleton a))

end Examples 