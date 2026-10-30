-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Pub/ReaderPin.lean: the reading of key file and entry file that asks the oracle, as a
family over the two public digests, which asks no public string.

Why. Johnson/TypedOracleCompiler/RecCompile/PublicPre.lean bounds a check on files of the shape: the public
algorithm asks the two public digests d = (c, p); then a reading at d of the files; then the arm at
d. It asks of the reading two things: at every d and on all files it asks no public string (`Pt2`,
Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublic.lean: the string s0 of the three public files' digest, and the
string `s1 c` of the parameters' digest at every c); and it asks at most a fixed number of strings.
The reading of Johnson/Top/Fire/ArmAskedAt.lean (the key file's table by a plain parse; the asking
half `typedER`; then `zOf`) is taken here at the parameters with the digest c. It asks the oracle
for every hash but one: the parameters' digest, which the public algorithm has just asked: there it
takes d.2 (`pinOn`, OnBytes/Slice/AtSet.lean): "do not ask twice". That it asks no other public
string is `typedER_onlyAtTypedOracleCompiler` (OnBytes/Tie/EntryAsks169.lean): of the strings of calls with the number
169 the asking half asks the one at its own parameter bytes alone, and both public strings are
strings of such calls.

Main names:
  `asksIn_pinOn_and`: an algorithm all of whose questions have a property P, with its questions at
    the strings of a set S answered by a table, asks only strings with P outside S.
  `s1_own`: the string at which the asking half asks its parameters' digest, at the parameters with
    the digest c, is `s1Of G c`.
  `zOfL`, `zOfL_eq`: `zOf` (ArmAskedAt.lean) over bare letters L and aL in the place of an input of
    the arm; at an input's own letters it is `zOf`.
  `readAtL`: the unpinned reading at the first public digest.
  `readPin`: the reading at d: `readAtL` with the one string `s1Of G d.1` answered with d.2.
  `readPin_asksIn`, `readPin_queries`: what PublicPre.lean asks: it asks no public string; it asks
    at most `typedT` strings (OnBytes/Tie/EntryAskedCost.lean), one number at all d and all files.
  `readPin_noCoin`: it tosses no coin. PublicPre.lean does not ask that of a reading; `AskReader`
    (Johnson/Top/Fire/ArmAsked.lean) does.
  `readPin_val`: its value under every oracle g: `zOfL` of the asking half's value `askedAt` at g
    with d.2 laid over at that one string.
  `readPin_pd`: in that value of the asking half the parameters' digest is d.2.
  `readPin_det_any`, `readPin_det`: under every oracle g, at a d whose second part is g's own answer
    at `s1Of G d.1`, the reading has the value of the unpinned reading; that at the oracle made from
    the format's hash.

What is not claimed. At a d whose second part is not the oracle's own answer the pinned and the
unpinned reading may differ; in the check d is what the public algorithm has just been answered. The
reading is a twin of the program's reader. Whether the program runs that twin's own text on a
model's entry file follows from what OnBytes/Main.lean calls (the head of
OnBytes/K/Oracle/ReaderAt.lean); the program does not call the reading. That it asks what the
program hashes is not claimed. The key file's table is parsed, no more. G, pol, lay, KL, the types I
and X, L, aL, recP and strP are letters. No yes is shown. No bound stands here
(Johnson/Top/Pub/ChkPublic.lean). All that the heads of ArmAskedAt.lean, PubStrings.lean,
EntryAsks169.lean and PublicPre.lean do not claim. Nothing on soundness here; no probability.
Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.Pub.PubStrings
import Johnson.Top.Fire.ArmAskedAt
import OnBytes.Tie.EntryAsks169

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom TypedOracleCompiler.Run TypedOracleCompiler.Slice TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Run (bytesToBits bytesToDig digToBytes oBits)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Tie OnBytes.K.Fire OnBytes.K.Oracle
open OnBytes.Slice (pinOn over_mem det_pinOn det_pinOn_of_eq queryBound_pinOn noCoin_pinOn)

/-- An algorithm all of whose questions have the property P, with its own questions at the strings
of S answered by a table and not asked, asks only strings that have P and lie outside S. -/
theorem asksIn_pinOn_and {lam : ℕ} {α : Type} (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (P : (o : (rom lam).ι) → (rom lam).Dom o → Prop) (c : OComp (rom lam) α) :
    c.AsksIn P → (pinOn S T c).AsksIn fun o s => P o s ∧ (s : List Bool) ∉ S := by
  induction c with
  | pure a => exact fun _ => trivial
  | query o s k ih =>
    intro h
    cases o
    by_cases hs : s ∈ S
    · simp only [pinOn, if_pos hs]
      exact ih _ (h.2 _)
    · simp only [pinOn, if_neg hs]
      exact ⟨⟨h.1, hs⟩, fun r => ih r (h.2 r)⟩
  | sample n k ih => exact fun h r => ih r (h r)

variable (G : EntryGround)

/-- The string at which the asking half asks its parameters' digest, at the parameters with the
digest c, is the second public string at c. -/
theorem s1_own (c : Dig 256) :
    bytesToBits (digestStr (linkAtCfg G.q (digToBytes c)).given.bytes) = s1Of G c := rfl

variable {I X : Type} {L : HolographicProtocol I X} {aL : RoundSplits L.link.shape}

/-- What the arm takes in, as a plain function of what the asking half returns: `zOf`
(Johnson/Top/Fire/ArmAskedAt.lean) over bare letters. -/
def zOfL (recP : Params.TableName → List (List E × E) → L.Rec)
    (strP : _root_.Fmt.ChainOut → Option (OneProtocolProof 256 (batLC L aL))) (a : AskedE) :
    Option (OutLA 256 L aL) :=
  (strP a.out).map fun π =>
    (bytesToDig a.first.root, bytesToDig a.further.root, recP a.first a.l0, recP a.further a.l1, π)

/-- At the letters of an input of the arm it is `zOf`. -/
theorem zOfL_eq (r : ArmIn) (recP : Params.TableName → List (List E × E) → r.L.Rec)
    (strP : _root_.Fmt.ChainOut → Option (OneProtocolProof 256 (batLC r.L r.aL))) :
    zOfL recP strP = zOf r recP strP := rfl

variable (recP : Dig 256 × Dig 256 → Params.TableName → List (List E × E) → L.Rec)
  (strP : Dig 256 × Dig 256 → _root_.Fmt.ChainOut → Option (OneProtocolProof 256 (batLC L aL)))

/-- The unpinned reading at the first public digest: the key file's table by a plain parse; the
asking half; then `zOfL`. -/
def readAtL (d : Dig 256 × Dig 256) (u : OnBytes.Slice.Shapes.Files) :
    OComp (rom 256) (Option (OutLA 256 L aL)) :=
  typedER (zOfL (recP d) (strP d)) (linkAtCfg G.q (digToBytes d.1))
    (keyAt G.q.link.table (digToBytes d.1) u.key).2.2 u.ent

/-- The reading at the two public digests d: the unpinned reading, with its questions at the string
of its own parameter bytes answered with d.2 and not asked. -/
def readPin (d : Dig 256 × Dig 256) (u : OnBytes.Slice.Shapes.Files) :
    OComp (rom 256) (Option (OutLA 256 L aL)) :=
  pinOn {s1Of G d.1} (fun _ => d.2) (readAtL G recP strP d u)

/-- It asks no public string, at every d and on all files, whatever the three public files. -/
theorem readPin_asksIn (pol lay KL : ByteArray) (d : Dig 256 × Dig 256)
    (u : OnBytes.Slice.Shapes.Files) :
    (readPin G recP strP d u).AsksIn fun _ s => ¬ Pt2 (s0Of pol lay KL) (s1Of G) s := by
  have h := asksIn_pinOn_and {s1Of G d.1} (fun _ => d.2) _ (readAtL G recP strP d u)
    (typedER_onlyAtTypedOracleCompiler (zOfL (recP d) (strP d)) (linkAtCfg G.q (digToBytes d.1))
      (keyAt G.q.link.table (digToBytes d.1) u.key).2.2 u.ent)
  refine OComp.AsksIn.mono (fun _ s hs hp => ?_) h
  have h169 : IsCall169 s := by
    rcases hp with rfl | ⟨c, rfl⟩
    · exact s0_call169 pol lay KL
    · exact s1_call169 G c
  exact hs.2 (Finset.mem_singleton.2 ((hs.1 h169).trans (s1_own G d.1)))

/-- It asks at most `typedT` strings: one number at every d and on all files. -/
theorem readPin_queries (d : Dig 256 × Dig 256) (u : OnBytes.Slice.Shapes.Files) :
    (readPin G recP strP d u).QueryBound (typedT G.q.link.table G.rs) :=
  queryBound_pinOn _ _ _ _ (G.typedER_asks _ _ _ _).2

/-- It tosses no coin. -/
theorem readPin_noCoin (d : Dig 256 × Dig 256) (u : OnBytes.Slice.Shapes.Files) :
    (readPin G recP strP d u).NoCoin :=
  noCoin_pinOn _ _ _ (G.typedER_asks _ _ _ _).1

/-- Its value under every oracle g: `zOfL` of the asking half's value at g with d.2 laid over at the
one string. -/
theorem readPin_val (d : Dig 256 × Dig 256) (u : OnBytes.Slice.Shapes.Files)
    (g : Fam (rom 256)) :
    (readPin G recP strP d u).det g =
      (askedAt (_root_.Run.oB (OnBytes.Slice.over {s1Of G d.1} (fun _ => d.2) g ()))
        (linkAtCfg G.q (digToBytes d.1)) (keyAt G.q.link.table (digToBytes d.1) u.key).2.2
        u.ent).bind (zOfL (recP d) (strP d)) := by
  unfold readPin readAtL
  rw [det_pinOn, typedER_det]

/-- In that value of the asking half, at every first table and entry file, the parameters' digest is
d.2. -/
theorem readPin_pd (d : Dig 256 × Dig 256) (g : Fam (rom 256)) (first : Params.TableName)
    (ent : ByteArray) (a : AskedE)
    (h : askedAt (_root_.Run.oB (OnBytes.Slice.over {s1Of G d.1} (fun _ => d.2) g ()))
      (linkAtCfg G.q (digToBytes d.1)) first ent = some a) :
    bytesToDig a.out.pd = d.2 := by
  rw [asked_pd _ _ _ _ _ h]
  unfold _root_.Run.oB
  rw [_root_.Run.TieTree.bytes_dig, s1_own G d.1]
  exact over_mem (fun _ => d.2) g (Finset.mem_singleton.2 rfl)

/-- Under every oracle g, at a d whose second part is g's own answer at the second public string at
d.1, the reading has the value of the unpinned reading: there the pin changes nothing. -/
theorem readPin_det_any (d : Dig 256 × Dig 256) (g : Fam (rom 256))
    (h2 : d.2 = g () (s1Of G d.1)) (u : OnBytes.Slice.Shapes.Files) :
    (readPin G recP strP d u).det g = (readAtL G recP strP d u).det g :=
  det_pinOn_of_eq _ _ _ (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact h2) _

/-- That at the oracle made from the format's hash. -/
theorem readPin_det (d : Dig 256 × Dig 256) (h2 : d.2 = oBits () (s1Of G d.1))
    (u : OnBytes.Slice.Shapes.Files) :
    (readPin G recP strP d u).det oBits = (readAtL G recP strP d u).det oBits :=
  readPin_det_any G recP strP d oBits h2 u

end OnBytes.K.Arm.Pub
