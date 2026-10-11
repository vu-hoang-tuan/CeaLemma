# CeaLemma — Hình thức hóa bổ đề Céa bằng Lean 4

CeaLemma là dự án chứng minh hình thức bổ đề Céa bằng **Lean 4** và **Mathlib**.
Kết quả chính mô tả tính gần tối ưu của xấp xỉ Galerkin: sai số của nghiệm xấp xỉ
được chặn bởi một hằng số nhân với sai số xấp xỉ tốt nhất trong không gian con đã chọn.

Dự án làm việc trên không gian vectơ định chuẩn thực. Mỗi proof được viết thành
một hạng chứng minh để Lean kiểm tra; đây là thư viện định lý, không phải chương trình
số dùng để tính nghiệm của một phương trình cụ thể.

## Phát biểu toán học

Cho $V$ là không gian vectơ định chuẩn trên $\mathbb{R}$,
$V_h \subseteq V$ là không gian con tuyến tính, và
$a : V \times V \to \mathbb{R}$ là dạng song tuyến tính. Giả sử:

- **Chặn liên tục:** tồn tại hằng số $M \ge 0$ sao cho
  $|a(w,v)| \le M\lVert w\rVert\lVert v\rVert$ với mọi $w,v \in V$.
- **Chặn cưỡng bức (coercivity):** có $\alpha > 0$ sao cho
  $\alpha\lVert v\rVert^2 \le a(v,v)$ với mọi $v \in V$.
- **Xấp xỉ thuộc không gian con:** $u_h \in V_h$.
- **Trực giao Galerkin:** $a(u-u_h,v_h)=0$ với mọi $v_h \in V_h$.

Khi đó:

$$
\lVert u-u_h\rVert
\le \frac{M}{\alpha}\inf_{v_h\in V_h}\lVert u-v_h\rVert.
$$

Đây là định lý `Cea.cea_lemma`. Trước khi lấy infimum, dự án chứng minh
`Cea.cea_pointwise` cho từng vectơ $v_h \in V_h$:

$$
\lVert u-u_h\rVert \le \frac{M}{\alpha}\lVert u-v_h\rVert.
$$

Hệ số $M/\alpha$ cho biết mức chênh lệch mà chặn sai số cho phép so với
khả năng xấp xỉ tốt nhất của $V_h$.

## Các khái niệm trong code

Tất cả định nghĩa và định lý của dự án nằm trong namespace `Cea`.

| Tên trong Lean | Ý nghĩa |
| --- | --- |
| `LinearMap.BilinForm ℝ V` | Dạng song tuyến tính thực trên `V`, do Mathlib cung cấp. |
| `Submodule ℝ V` | Không gian con tuyến tính `Vh`. |
| `Cea.HasContinuityBound a M` | Bất đẳng thức chặn liên tục của `a`. |
| `Cea.HasCoercivityBound a alpha` | Bất đẳng thức chặn cưỡng bức của `a`. |
| `Cea.IsGalerkinOrthogonal a Vh u uh` | Sai số `u - uh` trực giao với `Vh` theo dạng `a`. |
| `Cea.approxErrors Vh u` | Tập các giá trị `‖u - vh‖` với `vh ∈ Vh`. |
| `Cea.bestApproxError Vh u` | Infimum thực `sInf` của tập sai số xấp xỉ. |

Hai định nghĩa về chặn chỉ ghi nhận bất đẳng thức. Các điều kiện `0 ≤ M` và
`0 < alpha` được truyền riêng vào định lý. Tương tự, điều kiện `uh ∈ Vh`
được truyền riêng, không nằm trong định nghĩa trực giao Galerkin.

`bestApproxError` là định nghĩa `noncomputable`: dự án dùng infimum để phát biểu
và chứng minh chặn sai số, không đưa ra thuật toán tìm vectơ xấp xỉ tốt nhất.
Tập sai số không rỗng vì `0 ∈ Vh`, và bị chặn dưới bởi `0`.

## Mạch chứng minh

1. **Từ phương trình yếu đến trực giao Galerkin.** Với ánh xạ tuyến tính
   $L : V \to \mathbb{R}$, nếu $a(u,v)=L(v)$ với mọi $v\in V$ và
   $a(u_h,v_h)=L(v_h)$ với mọi $v_h\in V_h$, lấy hiệu hai đẳng thức cho
   `Cea.galerkin_orthogonality`.
2. **Đồng nhất thức sai số.** Với $e=u-u_h$ và $v_h\in V_h$, tính song tuyến tính
   cùng trực giao Galerkin cho $a(e,e)=a(e,u-v_h)$.
3. **Chặn cho từng vectơ.** Kết hợp cưỡng bức và liên tục để có
   $\alpha\lVert e\rVert^2\le M\lVert e\rVert\lVert u-v_h\rVert$.
   Proof xử lý riêng trường hợp $\lVert e\rVert=0$ trước khi khử nhân tử này.
4. **Chuyển sang infimum.** Khi $M>0$, thương
   $\lVert e\rVert/(M/\alpha)$ là chặn dưới của toàn bộ tập sai số xấp xỉ.
   Dùng tính chất của `sInf` rồi nhân lại với $M/\alpha$ để được kết quả cuối.
   Trường hợp $M=0$ được xử lý riêng, không chia cho hằng số bằng không.

## Phạm vi của kết quả

Định lý chính giả sử đã có `u`, `uh` và các điều kiện nêu trên. Dự án chưa chứng minh
sự tồn tại hay tính duy nhất của nghiệm của bài toán biến phân, và chưa hình thức hóa
một bài toán PDE hay lưới phần tử hữu hạn cụ thể.

Các proof hiện tại không cần giả thiết `V` đầy đủ, `a` đối xứng, hay `Vh` đóng hoặc
hữu hạn chiều. Trực giao ở đây được hiểu theo dạng song tuyến tính `a`.
Infimum không nhất thiết đạt được tại một vectơ trong `Vh`.

## Cấu trúc dự án

| Tệp | Nội dung |
| --- | --- |
| [`CeaLemma.lean`](CeaLemma.lean) | Module gốc, import toàn bộ thư viện và module kiểm tra. |
| [`CeaLemma/BilinearForm.lean`](CeaLemma/BilinearForm.lean) | Định nghĩa các chặn và bổ đề cơ bản về dạng song tuyến tính. |
| [`CeaLemma/Galerkin.lean`](CeaLemma/Galerkin.lean) | Trực giao Galerkin và đồng nhất thức sai số. |
| [`CeaLemma/CeaBound.lean`](CeaLemma/CeaBound.lean) | Chặn năng lượng `cea_energy_bound` và chặn từng vectơ `cea_pointwise`. |
| [`CeaLemma/CeaFinal.lean`](CeaLemma/CeaFinal.lean) | Tập sai số, sai số tốt nhất và định lý `cea_lemma`. |
| [`CeaLemma/Verify.lean`](CeaLemma/Verify.lean) | Lệnh kiểm tra kiểu, liệt kê tiên đề phụ thuộc và ví dụ áp dụng định lý. |
| [`lean-toolchain`](lean-toolchain) | Phiên bản Lean của dự án. |
| [`lakefile.toml`](lakefile.toml) | Cấu hình thư viện, phụ thuộc Mathlib và tùy chọn Lean. |
| [`lake-manifest.json`](lake-manifest.json) | Các commit phụ thuộc đã được khóa để tái lập môi trường. |

Có thể đọc các module theo thứ tự `BilinearForm`, `Galerkin`, `CeaBound`, `CeaFinal`,
sau đó xem ví dụ trong `Verify`.

## Cài đặt và build

Cài Git và [Lean thông qua elan](https://leanprover-community.github.io/get_started.html).
Nếu dùng VS Code, cài thêm extension **Lean 4** và mở thư mục gốc của dự án.

Phiên bản đang được cấu hình:

- Lean: `leanprover/lean4:v4.35.0-rc4`.
- Mathlib: tag `v4.35.0-rc4`; commit cụ thể được lưu trong `lake-manifest.json`.

Chạy các lệnh sau:

```bash
git clone https://github.com/vu-hoang-tuan/CeaLemma.git
cd CeaLemma
lake exe cache get
lake build
```

`elan` chọn toolchain từ `lean-toolchain`. Lệnh `lake exe cache get` tải cache
biên dịch sẵn của Mathlib; lần thiết lập đầu tiên cần kết nối Internet.
`lake build` biên dịch thư viện và kiểm tra các proof bằng Lean.
Giữ `lean-toolchain`, `lakefile.toml` và `lake-manifest.json` đồng bộ khi chủ động
nâng phiên bản phụ thuộc.

## Sử dụng và kiểm tra định lý

Trong một tệp Lean thuộc dự án, import module gốc:

```lean
import CeaLemma

#check Cea.galerkin_orthogonality
#check Cea.cea_pointwise
#check Cea.cea_lemma
```

Để dùng `Cea.cea_lemma`, cung cấp lần lượt dạng song tuyến tính, không gian con,
các hằng số, các chặn, hai vectơ và các giả thiết về nghiệm xấp xỉ.
[`CeaLemma/Verify.lean`](CeaLemma/Verify.lean) có một `example` đầy đủ theo đúng thứ tự
tham số này.

Sau khi build, có thể chạy trực tiếp module kiểm tra:

```bash
lake env lean CeaLemma/Verify.lean
```

Module dùng `#check` để hiển thị kiểu của các khai báo và `#print axioms Cea.cea_lemma`
để liệt kê các tiên đề mà proof phụ thuộc vào. Ví dụ trong module kiểm tra việc áp dụng
định lý với đầy đủ giả thiết.

## Quy ước trình bày

Code dùng module docstring `/-! ... -/`, docstring cho khai báo `/-- ... -/`, thụt lề
proof hai dấu cách và dòng Lean không quá 100 ký tự theo
[hướng dẫn phong cách Mathlib](https://leanprover-community.github.io/contribute/style.html).
Docstring trong code dùng tiếng Anh theo
[quy ước tài liệu Mathlib](https://leanprover-community.github.io/contribute/doc.html);
README này giải thích dự án bằng tiếng Việt.
