-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ShareNear.lean: from a proximity test's witness to the decoder's answer, member
by member, in the library's own terms. Statements and proofs.

No frame, no view and no program stands in it. There is no new mathematics: the library's lemma "a
share of a jointly close word is close" (`Site.share`, OnBytes/Slice/KeyGroup.lean) and its lemmas
on the decoder with a sample (Johnson/Desc/K12/Law/PinNear.lean).
Main names:
  `gp_share`: (near) `Site.share` at every member of a group (`Gp`), at the group's word (`Gp.word`;
    the library's `tie_word`): a witness within e positions of the group's word has, at member i, a
    share within the member's own radius of the member's sent word, if e < (the member's radius + 1)
    · 2 ^ (s.C.a − the member's tree's depth). The count is in the member's leaves: a leaf of a
    shorter tree is read at 2 ^ (s.C.a − a) positions of the range, so one leaf that parts costs
    that many positions; the library's lemma has it so.
  `mbOfShape`, `cd_mbOfShape`: a shape of the programs as the library's format of a sent message:
    its code is the oracle message's code (`portCode`) by definition.
  `pin_of_isDec`: a message within the radius (`Mb.IsDec`) with the sample's answers, at a seed
    without collision, is what `OMsg.dec` returns at `portOmZ cs sh e`.
  `gpOfList`, `decs_of_group`: the two together, over a signature `sigOf cs l` whose members have
    seats in a stage: from near the group's word, e fitting each radius in leaves, each share having
    its sample's answers, and `Sig.CF`: ∀ i, (sigOf cs l).decs σ f i = some (the member's share of
    the witness).
So the third clause of `PinSig` (Johnson/Desc/Sound/MsgSig.lean) is paid, in these terms, by: the
proximity test's witness (the test's law, read backwards); the sample rows among the batched rows
(the answers); `CfSig` (the sending's price; a file MeetsLaw.lean on it is not in this library).
Limits:
(1) The group here is `gpOfList`: the members' formats are `mbOfShape cs sh e` (the shape's own two
codes; depth `aOf cs sh`). The law's own group (`gpG`, Johnson/Desc/K12/Law/FirstOkLaw.lean) has the
stage's two codes and the tree's depth in these places. The two are one where a member has rows of
both kinds and its tree is as deep as the longer code; elsewhere they part in a field that no row
reads, and the types part with it. The join of the two groups is not typed.
(2) The premise ha (the answers): the tie between the programs' sample row and o.Z.val at `portZ` is
not looked for here.
(3) Only sampled messages are members: the folds' fresh masks and the base case's masking word are
pinned by nothing here.
(4) l, seat, f and σ are free letters.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `Site.share`, `Gp.tie_word`
(OnBytes/Slice/KeyGroup.lean); `pin_of_near`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.PinNear
import OnBytes.Slice.KeyGroup

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes.Slice Johnson.Pack

/-- (α) near, member by member, in leaves: the library's Site.share at every member of a group.
Let an encoding on the stage's tables be within e positions of the group's word. Each leaf of member
i's tree is read at 2 ^ (s.C.a − a i) positions of the range: if e is below (the member's radius +
1) times that number, the member's share of the witness is within the member's own radius of the
member's sent word, counted in the member's own leaves. -/
theorem gp_share {s : Sg} (G : Gp s) (hA : G.Apart) (yw : G.Words) (e : ℕ) (w : s.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext) (G.word yw) (s.cIn.enc w.1 w.2) ≤ e)
    (hfit : ∀ i, e < ((G.mb i).e + 1) * 2 ^ (s.C.a - (G.mb i).a)) :
    ∀ i, (G.mb i).IsDec (yw i) fun j => w.1 ((G.seat i).atJ j) :=
  fun i => (G.seat i).share ((G.tie_word hA yw).mem i) (hfit i) w hn

/-- A shape of the programs as the library's format of a sent message (Mb), at a radius: its code is
the code of the library's oracle message of that shape (portCode), by definition. -/
def mbOfShape (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e : ℕ) : Mb :=
  ⟨cMain cs sh, cMask cs sh, aOf cs sh, sh.mainRows, sh.maskRows, e⟩

theorem cd_mbOfShape (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e : ℕ) :
    (mbOfShape cs sh e).cd = portCode cs sh := rfl

/-- From the share to the pin: a message some encoding of which is within the radius of the word
as sent (read as a native word), with the sample's answers, at a seed without collision, is what the
library's decoder with the sample returns, at the oracle message of the shape. -/
theorem pin_of_isDec (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e : ℕ)
    (f : (portOmZ cs sh e).Str) (σ : (portOmZ cs sh e).Smp) (m : (portOmZ cs sh e).Msg)
    (hd : (mbOfShape cs sh e).IsDec ((portOmZ cs sh e).upW f) m)
    (ha : (portOmZ cs sh e).Z.val σ.1 m = σ.2) (hc : ¬ (portOmZ cs sh e).Clash f σ.1) :
    (portOmZ cs sh e).dec f σ = some m := by
  obtain ⟨r, hr⟩ := hd
  exact pin_of_near (portOmZ cs sh e) f σ (m, r) hr ha hc

/-- The group of a sending's sampled messages l, each with a seat in the stage s. -/
def gpOfList (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) {s : Sg}
    (seat : ∀ i : Fin l.length, Site s (mbOfShape cs (l.get i).1 (l.get i).2)) : Gp s where
  ι := Fin l.length
  mb := fun i => mbOfShape cs (l.get i).1 (l.get i).2
  seat := seat

/-- The pin behind a proximity test's witness, in the library's own terms. l: sampled messages'
shapes with their radii; each has a seat in the stage s, no two rows at one place; f: their words as
sent; σ: their samples. Let a witness on the stage's tables be within e positions of the group's
word made of these words; let e fit each member's radius in leaves; let each member's share have its
sample's answers; let the samples and words be collision-free (Sig.CF). Then every member's word
decodes, with its sample, to the member's share of the witness: the first half of Sig.over's relaxed
relation at sigOf cs l. -/
theorem decs_of_group (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) {s : Sg}
    (seat : ∀ i : Fin l.length, Site s (mbOfShape cs (l.get i).1 (l.get i).2))
    (hA : (gpOfList cs l seat).Apart) (f : (sigOf cs l).ext.Str) (σ : (sigOf cs l).Smp) (e : ℕ)
    (w : s.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext)
      ((gpOfList cs l seat).word fun i => ((sigOf cs l).om i).upW (f i)) (s.cIn.enc w.1 w.2) ≤ e)
    (hfit : ∀ i : Fin l.length, e < ((l.get i).2 + 1) * 2 ^ (s.C.a - aOf cs (l.get i).1))
    (ha : ∀ i, ((sigOf cs l).om i).Z.val (σ i).1 (fun j => w.1 ((seat i).atJ j)) = (σ i).2)
    (hc : (sigOf cs l).CF σ f) :
    ∀ i, (sigOf cs l).decs σ f i = some fun j => w.1 ((seat i).atJ j) :=
  fun i => pin_of_isDec cs (l.get i).1 (l.get i).2 (f i) (σ i) _
    (gp_share (gpOfList cs l seat) hA _ e w hn hfit i) (ha i) (hc i)

end H2K.Pin

#print axioms H2K.Pin.gp_share
#print axioms H2K.Pin.pin_of_isDec
#print axioms H2K.Pin.decs_of_group
