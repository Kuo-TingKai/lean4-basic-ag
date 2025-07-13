#!/bin/bash

# Lean4 代數幾何定理證明項目運行腳本

echo "=== Lean4 代數幾何定理證明項目 ==="
echo ""

# 檢查Lean4是否安裝
if ! command -v lean &> /dev/null; then
    echo "錯誤：未找到Lean4。請先安裝Lean4。"
    echo "訪問：https://leanprover.github.io/lean4/doc/quickstart.html"
    exit 1
fi

echo "Lean4版本："
lean --version
echo ""

# 檢查lake是否可用
if ! command -v lake &> /dev/null; then
    echo "錯誤：未找到lake。請確保Lean4安裝正確。"
    exit 1
fi

echo "=== 選擇要運行的示例 ==="
echo "1. 基本代數示例（無外部依賴）"
echo "2. 簡化代數幾何示例（少量依賴）"
echo "3. 完整代數幾何示例（需要mathlib）"
echo "4. 測試文件"
echo "5. 退出"
echo ""

read -p "請選擇 (1-5): " choice

case $choice in
    1)
        echo "運行基本代數示例..."
        lake exe lean --run Lean4App/BasicAlgebra.lean
        ;;
    2)
        echo "運行簡化代數幾何示例..."
        lake exe lean --run Lean4App/SimpleExamples.lean
        ;;
    3)
        echo "運行完整代數幾何示例..."
        echo "注意：這需要下載mathlib，可能需要一些時間和磁盤空間。"
        read -p "是否繼續？(y/n): " confirm
        if [ "$confirm" = "y" ] || [ "$confirm" = "Y" ]; then
            lake exe lean --run Lean4App/Examples.lean
        else
            echo "已取消。"
        fi
        ;;
    4)
        echo "運行測試文件..."
        lake exe lean --run Lean4App/Test.lean
        ;;
    5)
        echo "退出。"
        exit 0
        ;;
    *)
        echo "無效選擇。"
        exit 1
        ;;
esac

echo ""
echo "=== 運行完成 ===" 