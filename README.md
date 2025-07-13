# Lean4 代數幾何定理證明項目

這個項目使用Lean4證明代數幾何中的一些經典定理，並提供可執行的程式範例。

## 項目結構

```
lean4-app/
├── lakefile.lean          # Lean4項目配置文件
├── lean-toolchain         # Lean4工具鏈版本
├── Lean4App/
│   ├── AlgebraicGeometry.lean    # 代數幾何基本定理
│   ├── ClassicalTheorems.lean    # 經典定理證明
│   └── Examples.lean             # 具體示例和計算
└── README.md              # 項目說明
```

## 安裝和運行

### 1. 安裝Lean4

首先確保您已經安裝了Lean4。如果還沒有安裝，請訪問 [Lean4官網](https://leanprover.github.io/lean4/doc/quickstart.html) 進行安裝。

### 2. 克隆項目

```bash
git clone <repository-url>
cd lean4-app
```

### 3. 構建項目

**注意**：如果您的磁盤空間有限，建議先嘗試構建簡化版本：

```bash
# 構建基本版本（不依賴mathlib）
lake build Lean4App.BasicAlgebra

# 構建簡化版本（依賴較少的mathlib）
lake build Lean4App.SimpleExamples

# 構建完整版本（需要更多磁盤空間）
lake build
```

### 4. 運行示例

在項目目錄中運行：

```bash
# 運行基本代數示例（不需要外部依賴）
lake exe lean --run Lean4App/BasicAlgebra.lean

# 運行簡化示例
lake exe lean --run Lean4App/SimpleExamples.lean

# 運行完整示例（需要mathlib）
lake exe lean --run Lean4App/Examples.lean
```

或者在Lean4編輯器中打開文件進行交互式證明。

## 包含的定理

### 1. 多項式環的基本性質
- 零多項式的次數
- 常數多項式的次數
- 多項式加法的次數性質

### 2. 代數基本定理
- 代數閉域上的多項式分解
- 多項式根的重數

### 3. 希爾伯特零點定理
- 弱形式：非平凡理想有零點
- 強形式：根理想與理想的對應關係

### 4. 貝祖定理
- 代數曲線的交點數與次數的關係

### 5. 代數集的基本性質
- 代數集的定義和運算
- 代數集的交集性質
- 空代數集和全空間

### 6. 理想的基本運算
- 主理想的性質
- 理想的包含關係
- 理想的交集

### 7. 代數映射的性質
- 代數映射的定義
- 代數映射的零點
- 代數映射的複合

### 8. 代數擴張的性質
- 代數元素的定義
- 代數擴張的維數

### 9. 代數集的維數理論
- 代數集維數的定義
- 維數的基本性質

### 10. 代數簇的不可約性
- 不可約代數集的定義
- 單點集的不可約性

## 具體示例

項目中包含許多具體的計算示例：

### 多項式運算
```lean
-- 創建二次多項式
def quadratic_polynomial : Polynomial ℝ :=
  Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 1

-- 驗證次數
theorem quadratic_degree : quadratic_polynomial.degree = 2
```

### 代數基本定理的應用
```lean
-- 複數域上的多項式
def complex_polynomial : Polynomial ℂ :=
  Polynomial.X ^ 2 + Polynomial.C 1

-- 證明有根
theorem complex_polynomial_has_root :
  ∃ x : ℂ, complex_polynomial.eval x = 0
```

### 理想運算
```lean
-- 主理想的性質
theorem principal_ideal_example (a : ℝ) :
  a ∈ Ideal.span {a}
```

## 學習建議

1. **從基礎開始**：先閱讀 `Examples.lean` 中的具體示例，理解基本的證明技巧。

2. **理解概念**：通過 `AlgebraicGeometry.lean` 學習代數幾何的基本概念和定義。

3. **深入理論**：在 `ClassicalTheorems.lean` 中學習經典定理的證明。

4. **實踐練習**：嘗試修改和擴展現有的證明，或者證明新的定理。

## 依賴

- Lean4 v4.8.0
- mathlib v4.8.0

## 貢獻

歡迎提交問題報告和改進建議！如果您想貢獻代碼，請：

1. Fork 這個項目
2. 創建一個新的分支
3. 提交您的更改
4. 發起 Pull Request

## 參考資料

- [Lean4官方文檔](https://leanprover.github.io/lean4/doc/)
- [mathlib文檔](https://leanprover-community.github.io/mathlib4_docs/)
- [代數幾何入門](https://en.wikipedia.org/wiki/Algebraic_geometry)

## 許可證

這個項目採用 MIT 許可證。詳情請參見 LICENSE 文件。 