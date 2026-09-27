#include "share/atspre_staload.hats"
#use array as A
#use path as P
#use str as S

(* Joins "/foo" and "bar.txt" into "/foo/bar.txt", then takes the
   parent, filename and extension of the result, and checks
   is_absolute on it and on "bar.txt". Exits 1 on any mismatch. *)
fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

implement main0 () = let
  var bchars = @[char][4]('/', 'f', 'o', 'o')
  var nchars = @[char][7]('b', 'a', 'r', '.', 't', 'x', 't')
  var want = @[char][12]('/', 'f', 'o', 'o', '/', 'b', 'a', 'r', '.', 't', 'x', 't')
  val @(fzb, bwb) = $A.freeze<byte>($S.from_char_array(bchars, 4))
  val @(fzn, bwn) = $A.freeze<byte>($S.from_char_array(nchars, 7))
  val out = $A.alloc<byte>(16)
  val len = $P.join(bwb, 4, bwn, 7, out, 16)
  val @(fzo, bwo) = $A.freeze<byte>(out)
  val @(fzw, bww) = $A.freeze<byte>($S.from_char_array(want, 12))
  val @(head, tail) = $A.borrow_split<byte>(fzo, bwo, 12)
  val same = $S.eq(head, 12, bww, 12)
  val () = (if same then () else println! ("FAIL join: wrong bytes"))
  val r1 = check("join length", len, 12)
  val r2 = check("parent", $P.parent(head, 12), 4)
  val r3 = check("filename", $P.filename(head, 12), 5)
  val r4 = check("extension", $P.extension(head, 12), 9)
  val abs = $P.is_absolute(head, 12)
  val rel = $P.is_absolute(bwn, 7)
  val () = (if abs then () else println! ("FAIL is_absolute /foo/bar.txt"))
  val () = (if rel then println! ("FAIL is_absolute bar.txt") else ())
  val () = $A.drop<byte>(fzo, $A.borrow_join<byte>(fzo, head, tail))
  val () = $A.free<byte>($A.thaw<byte>(fzo))
  val () = $A.drop<byte>(fzw, bww) val () = $A.free<byte>($A.thaw<byte>(fzw))
  val () = $A.drop<byte>(fzb, bwb) val () = $A.free<byte>($A.thaw<byte>(fzb))
  val () = $A.drop<byte>(fzn, bwn) val () = $A.free<byte>($A.thaw<byte>(fzn))
in
  if same && r1 && r2 && r3 && r4 && abs && ~rel then println! ("ops: all cases pass")
  else exit_void(1)
end
