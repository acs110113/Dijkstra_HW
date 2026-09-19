# Dijkstra_HW

從 [shortest-path-competition](https://github.com/ythuang0522/shortest-path-competition) 的 `dijkstra_foundation.cpp` 修改而來的單檔 C++17 最短路徑作業。

## 目前狀態

`solver.cpp` 是待驗證版本，已通過編譯檢查，但最新版尚未完成 Linux 執行測試及正式評分。先前版本通過六筆開發測資；這不代表最新版已通過。尚無可提交的 `result.json`。

## 在 Linux 上測試與評分

Ubuntu 先安裝工具：

```bash
sudo apt update
sudo apt install -y git g++ make python3 curl gzip
```

在空的工作資料夾中執行：

```bash
git clone https://github.com/acs110113/Dijkstra_HW.git
git clone https://github.com/ythuang0522/shortest-path-competition.git
cp Dijkstra_HW/solver.cpp shortest-path-competition/solver.cpp
cd shortest-path-competition
g++ -O2 -std=c++17 -Wall -Wextra solver.cpp -o solver
python3 grade.py --solver ./solver --instances instances_dev.txt --json dev-result.json
```

先確認六筆開發測資均為 `ok`，再執行：

```bash
bash scripts/download_large.sh
python3 grade.py --solver ./solver --instances instances.txt --json result.json
```

正式六筆測資也必須全部為 `ok`。上傳同一次評分的 `solver.cpp` 與 `result.json`，評分後勿再修改原始碼。不要修改官方 `dijkstra_foundation.cpp`、`grade.py` 或測資。

## 優化方式

- 標準函式庫緩衝讀檔。
- 節點收縮與精確捷徑、階層式雙向 Dijkstra。
- 稀疏有向圖使用一般雙向 Dijkstra。
- 只有找到嚴格較短的替代路徑才刪除昂貴邊。
- 時間戳記避免逐次清空距離陣列；距離與捷徑使用 64 位元。

單一檔案、單執行緒，捷徑在執行時從輸入圖計算，沒有預存答案。
