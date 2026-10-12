# CeaLemma — Bổ đề Céa trong Lean và Mathlib

Dự án hình thức hóa chặn sai số gần tối ưu của phương pháp Galerkin, với mục tiêu
đóng góp module `Mathlib.Analysis.Normed.Operator.Cea` vào Mathlib.
Đây là thư viện định lý về xấp xỉ, không phải chương trình giải PDE bằng phương pháp số.

**Trạng thái:** đã sửa lỗi khử nhân tử và xung đột module được CI phát hiện trong
Phase 2, đồng thời bổ sung lint driver. Bản sửa này chưa được xác minh lại;
chưa có kết quả build, lint hoặc kiểm tra phụ thuộc tiên đề thành công.

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
Các đoạn Lean trong README là hướng dẫn sử dụng, chưa được biên dịch trong Phase 1.

## Tệp và môi trường

| Tệp | Vai trò |
| --- | --- |
| [`Mathlib/Analysis/Normed/Operator/Cea.lean`](Mathlib/Analysis/Normed/Operator/Cea.lean) | Toàn bộ phần toán học đề xuất cho Mathlib. |
| [`CeaLemma.lean`](CeaLemma.lean) | Module tiện ích của dự án, chỉ re-export module đóng góp. |
| [`lakefile.toml`](lakefile.toml) | Khai báo thư viện local `Cea`, wrapper `CeaLemma`, lint driver và tùy chọn Mathlib. |
| [`lake-manifest.json`](lake-manifest.json) | Khóa commit phụ thuộc. |
| [`lean-toolchain`](lean-toolchain) | Toolchain của Mathlib tại commit đích. |
| [`LICENSE`](LICENSE) | Giấy phép Apache 2.0. |

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

## Xác minh — tách biệt với lượt sửa

CI của commit `75517510d3f6d866e6608eab4a79f31258ed0c32` đã báo hai lỗi:
Lake tìm module mới trong dependency Mathlib thay vì nguồn downstream; bước khử
nhân tử dùng `mul_le_mul_iff_right₀` trong khi nhân tử chung nằm bên phải.
Bản sửa dùng module local `Cea` và `mul_le_mul_iff_left₀` tương ứng.
Phát biểu và giả thiết của các định lý được giữ nguyên.

CI trước đó bỏ qua `lake lint` vì chưa có lint driver. Cấu hình mới dùng
`batteries/runLinter` với đối số `Cea` để chọn các khai báo theo module nguồn,
kể cả các khai báo trong namespace `ContinuousLinearMap` và `IsCoercive`.
Các linter cú pháp trong `mathlibStandardSet`, header và độ dài tệp vẫn được bật.

Lượt sửa này không chạy build, lint hoặc kiểm tra proof. Mỗi lượt Phase 2 cần
yêu cầu riêng và không sửa tệp nguồn. Các lệnh chính dành cho Phase 2:

```bash
lake build
lake build Cea
lake lint
```

Ngoài các lệnh này, Phase 2 cần review phát biểu và giả thiết, kiểm tra phong cách,
placeholder và phụ thuộc tiên đề, đồng thời ghi nguyên lệnh cùng kết quả thực tế.
Cần xác minh riêng đường dẫn module khi tích hợp vào checkout Mathlib upstream.

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
GitHub hoặc Zulip. Ghi nhận này là tài liệu của repository. Theo yêu cầu của chủ dự án,
các bản sửa được đẩy lên nhánh `codex/mathlib-cea-phase1`; chưa mở PR upstream
hay đăng bình luận.
