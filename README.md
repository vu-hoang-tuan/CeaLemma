# CeaLemma — Bổ đề Céa trong Lean và Mathlib

Dự án hình thức hóa chặn sai số gần tối ưu của phương pháp Galerkin, với mục tiêu
đóng góp module `Mathlib.Analysis.Normed.Operator.Cea` vào Mathlib.
Đây là thư viện định lý về xấp xỉ, không phải chương trình giải PDE bằng phương pháp số.

**Trạng thái:** Phase 2 đã PASS cho mã nguồn tại commit
[`8d347c4`](https://github.com/vu-hoang-tuan/CeaLemma/commit/8d347c423a39a7d8ff16705c4eb806f085590ef0)
ngày 12/10/2026: build, lint và audit tiên đề downstream; build, lint khai báo,
kiểm tra phong cách và liệt kê tiên đề trong checkout Mathlib đích.
Xem [log Phase 2](https://github.com/vu-hoang-tuan/CeaLemma/actions/runs/38240537710).

## Phát biểu toán học

Cho $E$ là không gian vectơ nửa định chuẩn trên $\mathbb{R}$,
$K\subseteq E$ là không gian con tuyến tính và $B$ là dạng song tuyến tính liên tục.
Giả sử $\alpha>0$ và

$$
\alpha\lVert v\rVert^2\le B(v,v)\qquad (v\in E).
$$

Cho $u\in E$ và $u_h\in K$ thỏa mãn trực giao Galerkin:

$$
B(u-u_h,v)=0\qquad (v\in K).
$$

Với mọi $M\ge\lVert B\rVert$, bổ đề Céa cho chặn

$$
\lVert u-u_h\rVert
\le \frac{M}{\alpha}\inf_{v\in K}\lVert u-v\rVert.
$$

Có thể chọn $M=\lVert B\rVert$, là chuẩn toán tử của ánh xạ tuyến tính liên tục
$B:E\to(E\to\mathbb{R})$. Bản phát biểu dùng `Metric.infDist u (K : Set E)`
cho infimum bên phải. Tập `K` không rỗng vì chứa `0`.

Kết quả chỉ cần nửa định chuẩn, do đó bao gồm trường hợp không gian định chuẩn
của phiên bản trước. Không cần tính đầy đủ của `E`, tính đối xứng của `B`,
tính đóng hay hữu hạn chiều của `K`, hoặc sự tồn tại của vectơ đạt infimum.
Định lý giả sử đã có nghiệm và xấp xỉ thỏa mãn các điều kiện trên; nó không xây dựng chúng.

## API và quy ước tên

Mã nguồn dùng các khái niệm sẵn có của Mathlib:

| Thành phần | Biểu diễn trong Lean |
| --- | --- |
| Không gian thực | `[SeminormedAddCommGroup E] [NormedSpace ℝ E]` |
| Dạng song tuyến tính liên tục | `B : E →L[ℝ] E →L[ℝ] ℝ` |
| Không gian con | `K : Submodule ℝ E` |
| Chuẩn toán tử | `‖B‖` |
| Tính cưỡng bức | `IsCoercive B` |
| Sai số xấp xỉ tốt nhất | `Metric.infDist u (K : Set E)` |
| Trực giao Galerkin | `∀ v ∈ K, B (u - uₕ) v = 0` |

`IsCoercive B` đã được Mathlib định nghĩa bằng sự tồn tại của một hằng số dương
`α` thỏa `∀ v, α * ‖v‖ * ‖v‖ ≤ B v v`. Các định lý có hệ số tường minh nhận
`hα : 0 < α` và `hcoer` riêng để người dùng lựa chọn hằng số này.

Các tên định lý mô tả kết luận theo cách đặt tên của Mathlib; `infDist` giữ nguyên
cách viết của định nghĩa được nhắc tới. Namespace `Cea` và các predicate riêng
của phiên bản trước được loại bỏ.

| Định lý | Nội dung |
| --- | --- |
| `ContinuousLinearMap.norm_sub_le_mul_norm_sub_of_bound` | Chặn sai số bởi `(M / α) * ‖u - vₕ‖` với mọi `vₕ ∈ K`. |
| `ContinuousLinearMap.norm_sub_le_mul_infDist_of_bound` | Bổ đề Céa với `hcont : ‖B‖ ≤ M`. |
| `ContinuousLinearMap.norm_sub_le_mul_infDist` | Bổ đề Céa với hệ số `‖B‖ / α`. |
| `IsCoercive.exists_norm_sub_le_mul_infDist` | Một hằng số không âm dùng chung cho mọi không gian con và mọi xấp xỉ Galerkin của dạng cưỡng bức đã cho. |

Tên biến thống nhất: `E` cho không gian, `B` cho dạng song tuyến tính, `K` cho
không gian con, `u` cho nghiệm, `uₕ` cho xấp xỉ, `vₕ` cho vectơ so sánh,
`M` cho chặn chuẩn và `α` cho hằng số cưỡng bức. Các giả thiết tương ứng là
`hcont`, `hα`, `hcoer`, `huₕ`, `horth`, `hvₕ`.

## Mạch chứng minh

1. Với $e=u-u_h$ và $v_h\in K$, dùng $v_h-u_h\in K$ và trực giao Galerkin để có
   $B(e,e)=B(e,u-v_h)$.
2. Kết hợp chặn cưỡng bức và chặn chuẩn toán tử:
   $\alpha\lVert e\rVert^2\le M\lVert e\rVert\lVert u-v_h\rVert$.
   Nếu $\lVert e\rVert>0$, khử nhân tử này rồi chia cho $\alpha$;
   trường hợp chuẩn bằng không được xử lý riêng.
3. Dùng `Metric.isGLB_infDist` và `IsGLB.mul_left` để lấy infimum.
   Phép nhân chỉ đòi hỏi $M/\alpha\ge0$, nên không phải chia cho $M$ hay xử lý riêng $M=0$.
4. Từ `IsCoercive B`, lấy một hằng số cưỡng bức rồi chọn hệ số gần tối ưu `‖B‖ / α`.

Các bổ đề bao quanh tính song tuyến tính, chặn tại vectơ sai số và infimum tự định nghĩa
được thay bằng API Mathlib. Các module cũ `BilinearForm`, `Galerkin`, `CeaBound`,
`CeaFinal` và `Verify` được loại bỏ; thư viện chỉ chứa module đóng góp và wrapper.

## Sử dụng và chuyển từ API cũ

Trong repository downstream, import module gốc:

```lean
import CeaLemma
```

Lake biên dịch tệp `Mathlib/Analysis/Normed/Operator/Cea.lean` thành module local
`Cea` qua `srcDir`; wrapper `CeaLemma` re-export module này. Cách cấu hình này tránh
tranh chấp tiền tố module `Mathlib` với dependency, không sao chép mã nguồn hoặc
đổi namespace định lý. Khi đưa tệp vào Mathlib upstream, đường dẫn import là
`Mathlib.Analysis.Normed.Operator.Cea`.

Khi đã có `hα`, `hcoer`, `huₕ` và `horth` như trên, áp dụng:

```lean
exact B.norm_sub_le_mul_infDist hα hcoer huₕ horth
```

Để giữ hệ số `M / α`, cung cấp thêm `hcont : ‖B‖ ≤ M`:

```lean
exact B.norm_sub_le_mul_infDist_of_bound hcont hα hcoer huₕ horth
```

Nếu xuất phát từ phương trình yếu `hexact : ∀ v, B u v = f v` và
`hdiscrete : ∀ v ∈ K, B uₕ v = f v`, trực giao Galerkin được suy ra bằng API sẵn có:

```lean
have horth : ∀ v ∈ K, B (u - uₕ) v = 0 := by
  intro v hv
  rw [B.map_sub₂, hexact v, hdiscrete v hv, sub_self]
```

Không cần giả thiết bổ sung về `f` để lấy hiệu hai phương trình này.

Đối với dạng song tuyến tính đại số `a : LinearMap.BilinForm ℝ E` của API cũ,
chặn `|a v w| ≤ M * ‖v‖ * ‖w‖` cho phép dùng `LinearMap.mkContinuous₂` để tạo `B`.
`LinearMap.mkContinuous₂_apply` giữ nguyên giá trị của dạng, còn
`LinearMap.mkContinuous₂_norm_le` cho `‖B‖ ≤ M` khi `0 ≤ M`.
Do đó việc chuyển sang dạng liên tục không đòi hỏi thêm giả thiết toán học.
Với `B` đã được đóng gói, `0 ≤ M` suy ra từ `‖B‖ ≤ M` nên không cần truyền riêng.
Chặn cưỡng bức dùng tích `α * ‖v‖ * ‖v‖`, tương đương `α * ‖v‖ ^ 2`.

`Metric.infDist` thay thế tập `approxErrors` và `bestApproxError`; trên không gian con
không rỗng, nó biểu diễn cùng infimum khoảng cách. Các tên cũ được bỏ, không giữ alias.
Các đoạn Lean trong README là hướng dẫn sử dụng; workflow kiểm tra các module nguồn,
không biên dịch riêng từng đoạn ví dụ trong README.

## Tệp và môi trường

| Tệp | Vai trò |
| --- | --- |
| [`Mathlib/Analysis/Normed/Operator/Cea.lean`](Mathlib/Analysis/Normed/Operator/Cea.lean) | Toàn bộ phần toán học đề xuất cho Mathlib. |
| [`CeaLemma.lean`](CeaLemma.lean) | Module tiện ích của dự án, chỉ re-export module đóng góp. |
| [`lakefile.toml`](lakefile.toml) | Khai báo thư viện local `Cea`, wrapper `CeaLemma`, lint driver và tùy chọn Mathlib. |
| [`lake-manifest.json`](lake-manifest.json) | Khóa commit phụ thuộc. |
| [`lean-toolchain`](lean-toolchain) | Toolchain của Mathlib tại commit đích. |
| [`LICENSE`](LICENSE) | Giấy phép Apache 2.0. |
| [`.github/workflows/phase2-verification.yml`](.github/workflows/phase2-verification.yml) | Build, lint và audit tiên đề; kiểm tra module trong checkout Mathlib đích. |

Đích là Mathlib `master` tại commit
[`dde65624ecc7ebb09c14a4c2d5a13bedc94c939c`](https://github.com/leanprover-community/mathlib4/commit/dde65624ecc7ebb09c14a4c2d5a13bedc94c939c),
đọc ngày 12/10/2026. Toolchain của commit này là `leanprover/lean4:v4.35.0-rc4`.
Cấu hình và manifest khóa cùng commit để tái lập môi trường; không dùng tag phát hành
làm mốc Mathlib cho bản đóng góp này. Các workflow phát hành/cập nhật tag hiện có là
hạ tầng của repository downstream, không thuộc module đề xuất cho Mathlib.

Mã toán học nằm trong `Analysis/Normed/Operator` vì chỉ cần cấu trúc nửa định chuẩn,
không cần cấu trúc tích vô hướng của module `InnerProductSpace/LaxMilgram`.
Khi đưa module vào checkout upstream, cần thêm
`public import Mathlib.Analysis.Normed.Operator.Cea` vào danh sách import của
`Mathlib.lean`. Wrapper `CeaLemma.lean`, cấu hình Lake và workflow downstream không
thuộc phần đóng góp upstream.

## Kết quả xác minh và cách chạy lại

[Phase 2 tại commit `8d347c4`](https://github.com/vu-hoang-tuan/CeaLemma/actions/runs/38240537710)
hoàn tất thành công ngày 12/10/2026 với Lean 4.35.0-rc4 và Mathlib tại commit đã khóa.

| Kiểm tra | Kết quả |
| --- | --- |
| `lake build` trong dự án | PASS — 1934 jobs, gồm `Cea` và `CeaLemma`. |
| `lake lint` | PASS — linter chạy trên module `Cea`. |
| `axiom-audit` | PASS — kiểm tra cả bốn khai báo. |
| `lake build Mathlib.Analysis.Normed.Operator.Cea` trong checkout upstream | PASS — 1931 jobs. |
| `lake exe batteries/runLinter --no-build Mathlib.Analysis.Normed.Operator.Cea` | PASS. |
| `lake exe lint-style Mathlib.CeaPhase2Imports` | PASS — driver tạm import module đóng góp để chọn đúng tệp cần lint. |
| `lake env lean --stdin` với bốn lệnh `#print axioms` | PASS. |
| `git diff --exit-code` trên dự án sau kiểm tra | PASS — không sửa mã nguồn trong quá trình xác minh. |

Cả bốn định lý chỉ phụ thuộc `propext`, `Classical.choice` và `Quot.sound`;
audit không phát hiện `sorryAx` hoặc tiên đề ngoài danh sách cho phép.
Log không có lỗi hay cảnh báo. Kết quả này áp dụng cho snapshot đã ghi rõ ở trên.

Sau khi cài Lean qua `elan`, chạy trong thư mục dự án:

```bash
lake exe cache get
lake build
lake build Cea
lake lint
```

Workflow `Phase 2 verification` chạy khi mã Lean, cấu hình toolchain/dependency hoặc
chính workflow thay đổi trên `main` hay trong PR vào `main`; có thể chạy thủ công
qua `workflow_dispatch`. Workflow kiểm tra đúng commit kích hoạt, sao chép nguyên
module vào checkout Mathlib tạm và kiểm tra mã nguồn dự án không bị sửa.

Lượt sửa và lượt xác minh được tách biệt. Trước khi nộp vào Mathlib, người đóng góp
cần review proof và thêm import tương ứng vào `Mathlib.lean`; khi đổi snapshot
Mathlib hoặc mã nguồn, cần chạy lại các kiểm tra.

## Quy ước đóng góp và hỗ trợ AI

Tên và cấu trúc module dựa trên các API hiện có trong
`Mathlib.Analysis.Normed.Operator.NormedSpace`,
`Mathlib.Analysis.Normed.Operator.Bilinear` và
`Mathlib.Topology.MetricSpace.HausdorffDistance` tại commit đã khóa.
Tài liệu trong Lean dùng tiếng Anh; README dùng tiếng Việt.

Tham khảo hướng dẫn chính thức về
[đóng góp và chính sách AI](https://leanprover-community.github.io/contribute/index.html),
[phong cách](https://leanprover-community.github.io/contribute/style.html),
[đặt tên](https://leanprover-community.github.io/contribute/naming.html) và
[tài liệu](https://leanprover-community.github.io/contribute/doc.html).

**Ghi nhận hỗ trợ AI:** OpenAI Codex được dùng để đọc nguồn Mathlib, đề xuất và viết
bản refactor Lean, đổi tên API, cập nhật cấu hình và viết lại README này.
Đây là thay đổi có phần code đáng kể do LLM tạo. Review tĩnh bằng Codex không thay
thế review của người am hiểu Lean hoặc kiểm tra proof bằng Lean.

Trước khi nộp upstream, người đóng góp cần tự hiểu và chịu trách nhiệm về code,
khai báo công cụ và phạm vi sử dụng AI trong mô tả PR, và áp dụng nhãn `LLM-generated`
theo chính sách Mathlib. Chính sách không cho phép dùng LLM để viết bình luận trên
GitHub hoặc Zulip. Ghi nhận này là tài liệu của repository; lịch sử commit lưu
các thay đổi có hỗ trợ AI. Chưa mở PR upstream hay đăng bình luận.
