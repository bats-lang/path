(* path -- file path manipulation *)
(* Pure byte scanning on borrowed byte arrays. No $UNSAFE, no assume. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use str as S

(* ============================================================
   Constants: ASCII codes
   ============================================================ *)

#define SLASH 47
#define DOT 46

(* ============================================================
   join -- join base and name with / separator into out, which must
   have room for both and the separator: the length written,
   base_len + 1 + name_len.
   ============================================================ *)

#pub fun join
  {la:agz}{na:pos}{lb:agz}{nb:pos}{lo:agz}{mo:pos | na + nb + 1 <= mo}
  (base: !$A.borrow(byte, la, na), base_len: int na,
   name: !$A.borrow(byte, lb, nb), name_len: int nb,
   out: !$A.arr(byte, lo, mo), max: int mo): int(na + nb + 1)

(* ============================================================
   parent -- return length of parent (up to last /)
   e.g. "/foo/bar" -> 4 ("/foo")
   ============================================================ *)

#pub fun parent
  {la:agz}{na:pos}
  (path: !$A.borrow(byte, la, na), path_len: int na): [r:nat | r < na] int r

(* ============================================================
   filename -- return offset of filename (after last /)
   e.g. "/foo/bar.txt" -> 5
   ============================================================ *)

#pub fun filename
  {la:agz}{na:pos}
  (path: !$A.borrow(byte, la, na), path_len: int na): [r:nat | r <= na] int r

(* ============================================================
   extension -- return offset of extension (after last .)
   e.g. "/foo/bar.txt" -> 9
   Returns path_len if no extension found.
   ============================================================ *)

#pub fun extension
  {la:agz}{na:pos}
  (path: !$A.borrow(byte, la, na), path_len: int na): [r:nat | r <= na] int r

(* ============================================================
   is_absolute -- starts with /
   ============================================================ *)

#pub fun is_absolute
  {la:agz}{na:pos}
  (path: !$A.borrow(byte, la, na), path_len: int na): bool

(* ============================================================
   Implementations
   ============================================================ *)

(* -- join -- *)

implement join {la}{na}{lb}{nb}{lo}{mo}
  (base, base_len, name, name_len, out, max) = let
  fun copy_base {lo:agz}{mo:pos}{la:agz}{na:pos | na < mo}{i:nat | i <= na} .<na - i>.
    (out: !$A.arr(byte, lo, mo),
     base: !$A.borrow(byte, la, na), base_len: int na,
     i: int i): void =
    if i >= base_len then ()
    else let
      val b = $A.read<byte>(base, i)
      val () = $A.set<byte>(out, i, b)
    in copy_base(out, base, base_len, $AR.add_g1(i, 1)) end

  fun copy_name {lo:agz}{mo:pos}{lb:agz}{nb:pos}{off:nat | off + nb <= mo}{i:nat | i <= nb} .<nb - i>.
    (out: !$A.arr(byte, lo, mo),
     name: !$A.borrow(byte, lb, nb), name_len: int nb,
     i: int i, offset: int off): void =
    if i >= name_len then ()
    else let
      val b = $A.read<byte>(name, i)
      val di = $AR.add_g1(offset, i)
      val () = $A.set<byte>(out, di, b)
    in copy_name(out, name, name_len, $AR.add_g1(i, 1), offset) end
  val () = copy_base(out, base, base_len, 0)
  val () = $A.set<byte>(out, base_len, $A.int2byte($AR.byte_of_char('/')))
  val offset = $AR.add_g1(base_len, 1)
  val () = copy_name(out, name, name_len, 0, offset)
in $AR.add_g1(offset, name_len) end

(* -- parent -- *)

implement parent {la}{na} (path, path_len) = let
  fun loop {la:agz}{na:pos}{i:nat | i <= na} .<i>.
    (path: !$A.borrow(byte, la, na),
     i: int i): [r:nat | r < na] int r =
    if $AR.lte_g1(i, 0) then 0
    else let
      val idx = $AR.sub_g1(i, 1)
      val c = byte2int0($A.read<byte>(path, idx))
    in
      if $AR.eq_int_int(c, SLASH) then idx
      else loop(path, idx)
    end
in loop(path, path_len) end

(* -- filename -- *)

implement filename {la}{na} (path, path_len) = let
  fun loop {la:agz}{na:pos}{i:nat | i <= na} .<i>.
    (path: !$A.borrow(byte, la, na),
     i: int i): [r:nat | r <= na] int r =
    if $AR.lte_g1(i, 0) then 0
    else let
      val idx = $AR.sub_g1(i, 1)
      val c = byte2int0($A.read<byte>(path, idx))
    in
      if $AR.eq_int_int(c, SLASH) then i
      else loop(path, idx)
    end
in loop(path, path_len) end

(* -- extension -- *)

implement extension {la}{na} (path, path_len) = let
  val fname_start = filename(path, path_len)
  fun loop {la:agz}{na:pos}{i:nat | i <= na}{f:nat} .<i>.
    (path: !$A.borrow(byte, la, na), path_len: int na,
     i: int i, fname_start: int f): [r:nat | r <= na] int r =
    if $AR.lte_g1(i, 0) then path_len
    else if $AR.lte_g1(i, fname_start) then path_len
    else let
      val idx = $AR.sub_g1(i, 1)
      val c = byte2int0($A.read<byte>(path, idx))
    in
      if $AR.eq_int_int(c, DOT) then i
      else loop(path, path_len, idx, fname_start)
    end
in loop(path, path_len, path_len, fname_start) end

(* -- is_absolute -- *)

implement is_absolute {la}{na} (path, path_len) = let
  val c = byte2int0($A.read<byte>(path, 0))
in $AR.eq_int_int(c, SLASH) end

(* ============================================================
   Static tests
   ============================================================ *)

fn _test_parent(): void = let
  (* Test with "/foo/bar" = [47,102,111,111,47,98,97,114] len=8 *)
  var chars = @[char][8]('/', 'f', 'o', 'o', '/', 'b', 'a', 'r')
  val arr = $S.from_char_array(chars, 8)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val p = parent(bw, 8)
  val () = $A.drop<byte>(fz, bw)
  val arr2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(arr2)
in end

fn _test_filename(): void = let
  var chars = @[char][8]('/', 'f', 'o', 'o', '/', 'b', 'a', 'r')
  val arr = $S.from_char_array(chars, 8)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val f = filename(bw, 8)
  val () = $A.drop<byte>(fz, bw)
  val arr2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(arr2)
in end

fn _test_is_absolute(): void = let
  var chars = @[char][4]('/', 'f', 'o', 'o')
  val arr = $S.from_char_array(chars, 4)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val b = is_absolute(bw, 4)
  val () = $A.drop<byte>(fz, bw)
  val arr2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(arr2)
in end

fn _test_join(): void = let
  var bchars = @[char][3]('f', 'o', 'o')
  val base = $S.from_char_array(bchars, 3)
  var nchars = @[char][3]('b', 'a', 'r')
  val name = $S.from_char_array(nchars, 3)
  val out = $A.alloc<byte>(7)
  val @(fzb, bwb) = $A.freeze<byte>(base)
  val @(fzn, bwn) = $A.freeze<byte>(name)
  val len = join(bwb, 3, bwn, 3, out, 7)
  val () = $A.drop<byte>(fzb, bwb)
  val () = $A.drop<byte>(fzn, bwn)
  val base2 = $A.thaw<byte>(fzb)
  val name2 = $A.thaw<byte>(fzn)
  val () = $A.free<byte>(base2)
  val () = $A.free<byte>(name2)
  val () = $A.free<byte>(out)
in end

fn _test_extension(): void = let
  (* "/foo/bar.txt" = [47,102,111,111,47,98,97,114,46,116,120,116] len=12 *)
  var chars = @[char][12]('/', 'f', 'o', 'o', '/', 'b', 'a', 'r', '.', 't', 'x', 't')
  val arr = $S.from_char_array(chars, 12)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val e = extension(bw, 12)
  val () = $A.drop<byte>(fz, bw)
  val arr2 = $A.thaw<byte>(fz)
  val () = $A.free<byte>(arr2)
in end

(* ============================================================
   Tests (bats test)
   ============================================================ *)

$UNITTEST.run begin

(* "/foo/bar.txt" as a 12-byte array, and n *)
fn with_path {n:pos | n <= 12} (n: int n): @([l:agz] $A.arr(byte, l, 12), int n) = let
  var chars = @[char][12]('/', 'f', 'o', 'o', '/', 'b', 'a', 'r', '.', 't', 'x', 't')
in @($S.from_char_array(chars, 12), n) end

fn test_parent (): bool = let
  val @(arr, _) = with_path(12)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val p = parent(bw, 12)
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in p = 4 end

fn test_parent_none (): bool = let
  var chars = @[char][3]('f', 'o', 'o')
  val @(fz, bw) = $A.freeze<byte>($S.from_char_array(chars, 3))
  val p = parent(bw, 3)
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in p = 0 end

fn test_filename (): bool = let
  val @(arr, _) = with_path(12)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val f = filename(bw, 12)
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in f = 5 end

fn test_extension (): bool = let
  val @(arr, _) = with_path(12)
  val @(fz, bw) = $A.freeze<byte>(arr)
  val e = extension(bw, 12)
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in e = 9 end

(* "/foo.d/bar": the dot is in a directory, so there is no extension *)
fn test_extension_none (): bool = let
  var chars = @[char][10]('/', 'f', 'o', 'o', '.', 'd', '/', 'b', 'a', 'r')
  val @(fz, bw) = $A.freeze<byte>($S.from_char_array(chars, 10))
  val e = extension(bw, 10)
  val () = $A.drop<byte>(fz, bw)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in e = 10 end

fn test_is_absolute (): bool = let
  var a = @[char][4]('/', 'f', 'o', 'o')
  var r = @[char][3]('f', 'o', 'o')
  val @(fa, ba) = $A.freeze<byte>($S.from_char_array(a, 4))
  val @(fr, br) = $A.freeze<byte>($S.from_char_array(r, 3))
  val ok = is_absolute(ba, 4) && ~is_absolute(br, 3)
  val () = $A.drop<byte>(fa, ba)
  val () = $A.free<byte>($A.thaw<byte>(fa))
  val () = $A.drop<byte>(fr, br)
  val () = $A.free<byte>($A.thaw<byte>(fr))
in ok end

(* "foo" + "bar" is "foo/bar", 7 bytes *)
fn test_join (): bool = let
  var bchars = @[char][3]('f', 'o', 'o')
  var nchars = @[char][3]('b', 'a', 'r')
  val @(fzb, bwb) = $A.freeze<byte>($S.from_char_array(bchars, 3))
  val @(fzn, bwn) = $A.freeze<byte>($S.from_char_array(nchars, 3))
  val out = $A.alloc<byte>(7)
  val len = join(bwb, 3, bwn, 3, out, 7)
  var want = @[char][7]('f', 'o', 'o', '/', 'b', 'a', 'r')
  val w = $S.from_char_array(want, 7)
  val @(fzo, bwo) = $A.freeze<byte>(out)
  val @(fzw, bww) = $A.freeze<byte>(w)
  val same = $S.eq(bwo, 7, bww, 7)
  val () = $A.drop<byte>(fzo, bwo)
  val () = $A.free<byte>($A.thaw<byte>(fzo))
  val () = $A.drop<byte>(fzw, bww)
  val () = $A.free<byte>($A.thaw<byte>(fzw))
  val () = $A.drop<byte>(fzb, bwb)
  val () = $A.free<byte>($A.thaw<byte>(fzb))
  val () = $A.drop<byte>(fzn, bwn)
  val () = $A.free<byte>($A.thaw<byte>(fzn))
in len = 7 && same end

end
