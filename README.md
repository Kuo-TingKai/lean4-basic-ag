# Lean4 代數幾何定理證明項目

這個項目使用Lean4證明代數幾何中的一些經典定理，並提供可執行的程式範例。

## 專案進度狀態

### ✅ 已完成
- [x] 項目基礎架構設置
- [x] Git 倉庫初始化和 GitHub 推送
- [x] Lean4 工具鏈配置 (v4.8.0)
- [x] mathlib 依賴配置 (v4.8.0)
- [x] 基本代數定理證明 (`BasicAlgebra.lean`)
- [x] 可執行程序配置和運行
- [x] 語法錯誤修復和編譯成功

### 🔄 進行中
- [ ] 代數幾何核心定理證明
- [ ] 互動式證明檢查
- [ ] 更多計算示例

### 📋 待完成
- [ ] 完整代數幾何定理庫
- [ ] 測試套件
- [ ] 文檔完善
- [ ] 性能優化

## 項目結構

```
lean4-app/
├── lakefile.lean          # Lean4項目配置文件
├── lean-toolchain         # Lean4工具鏈版本
├── Lean4App/
│   ├── BasicAlgebra.lean      # ✅ 基本代數定理證明 (可執行)
│   ├── AlgebraicGeometry.lean # 📋 代數幾何基本定理
│   ├── ClassicalTheorems.lean # 📋 經典定理證明
│   ├── Examples.lean          # 📋 具體示例和計算
│   ├── SimpleExamples.lean    # 📋 簡化示例
│   ├── Test.lean              # 📋 測試文件
│   └── lean4_app.lean         # 📋 主模組文件
├── main.lean              # 📋 主程序入口
├── run_examples.sh        # 📋 運行腳本
├── PROJECT_SUMMARY.md     # 📋 項目摘要
└── README.md              # 項目說明
```

## 快速開始

### 1. 安裝Lean4

首先確保您已經安裝了Lean4。如果還沒有安裝，請訪問 [Lean4官網](https://leanprover.github.io/lean4/doc/quickstart.html) 進行安裝。

### 2. 克隆項目

```bash
git clone <repository-url>
cd lean4-app
```

### 3. 構建項目

```bash
# 構建完整項目
lake build

# 構建特定模組
lake build Lean4App.BasicAlgebra
```

### 4. 運行示例

```bash
# 運行基本代數示例 (✅ 已測試成功)
lake exe basic_algebra

# 輸出示例:
# === Lean4 基本代數定理證明 ===
# 定理1: 自然數加法零元素
# 3 + 0 = 3
# 定理2: 自然數乘法分配律
# 2 * (3 + 4) = 14
# 2 * 3 + 2 * 4 = 14
# 定理11: 斐波那契數列
# fibonacci 5 = 5
# fibonacci 6 = 8
# 定理12: 階乘
# factorial 5 = 120
# factorial 6 = 720
# 所有定理證明完成！
```

### 5. 互動式證明檢查

在 Cursor 或 VSCode 中：
1. 安裝 Lean4 擴展
2. 打開 `Lean4App/BasicAlgebra.lean`
3. 等待 Lean4 服務器啟動
4. 使用互動式證明功能檢查定理

## 已完成的內容

### BasicAlgebra.lean ✅
包含以下已證明的定理：

1. **自然數基本性質**
   - 加法零元素：`n + 0 = n`
   - 乘法分配律：`a * (b + c) = a * b + a * c`
   - 加法結合律：`(a + b) + c = a + (b + c)`
   - 加法交換律：`a + b = b + a`
   - 乘法結合律：`(a * b) * c = a * (b * c)`

2. **集合論基本概念**
   - 集合包含關係的定義
   - 集合包含的自反性
   - 集合包含的傳遞性

3. **函數基本概念**
   - 函數複合的定義
   - 函數複合的結合律

4. **邏輯基本定理**
   - 雙重否定：`¬¬P ↔ P`
   - 德摩根律：`¬(P ∧ Q) ↔ ¬P ∨ ¬Q`

5. **具體計算示例**
   - 斐波那契數列計算和性質
   - 階乘計算和性質

## 技術細節

### 編譯狀態
- ✅ `lake build` 成功
- ✅ 語法檢查通過
- ✅ 類型檢查通過
- ✅ 可執行程序正常運行

### 依賴管理
- Lean4 v4.8.0
- mathlib v4.8.0
- Lake 構建系統

### 文件狀態
- `BasicAlgebra.lean`: ✅ 完整且可執行
- 其他文件: 📋 待開發

## 包含的定理 (計劃)

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

## 學習建議

1. **從基礎開始**：先運行 `lake exe basic_algebra` 查看基本代數定理的證明和計算。

2. **理解概念**：通過 `BasicAlgebra.lean` 學習基本的證明技巧和邏輯結構。

3. **互動式學習**：在編輯器中打開文件，使用 Lean4 的互動式證明功能。

4. **實踐練習**：嘗試修改和擴展現有的證明，或者證明新的定理。

## 故障排除

### 常見問題

1. **"unknown package 'Mathlib'" 錯誤**
   - 解決方案：使用 `lake build` 而不是 `lean --run`

2. **"unknown executable lean" 錯誤**
   - 解決方案：使用 `lake exe basic_algebra` 執行

3. **語法錯誤**
   - 解決方案：確保使用正確的 import 路徑

### 開發環境設置

在 Cursor 中設置 Lean4：
1. 安裝 Lean4 擴展
2. 打開項目文件夾
3. 等待 Lean4 服務器啟動
4. 使用互動式證明功能

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