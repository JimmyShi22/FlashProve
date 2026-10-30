-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/BehindSig.lean: the two sides behind the code switch, at the plain letters,
in the terms of Johnson/Desc/Sound/MsgSig.lean.
The law of the code switch (KeepsAt.lean, BehindPaid.lean) speaks behind the block of the signature
`(selLoc X iJ iQ).S`: the old open messages beside the new ones. At the plain letters
(`Letters.plain`, Member.lean) no old message is open (`plain_empty`, PlainAt.lean) and the carried
base joint asks nothing. So what is said behind is said of the new members `sigOf r.cs r.l` alone.
`fbMade`: the reading of a statement behind, by make: `fbOf` at the words `strMadeB`
(WordsMade.lean).
`pb_iff_cf`: the promise behind (`lawPb`) at it is `Sig.CF` of the new members, at the
out-of-domain (OOD) samples `newSmp` and the words `wordsOf`.
`wtMade`: the witness behind made of a witness of the table of joints: the new members' messages
`msgsOf`, each with randomness 0.
`rb_decs_iff`: the first clause of what stands behind (`lawRb`) at it says that each new member's
word decodes, with its OOD sample, to `msgsOf`. `rb_carried`: the third clause holds.
Limits. Unfoldings at the plain letters alone. The second clause of `lawRb` (the rows) is not
touched. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.WordsMade
import Johnson.Top.H0.K2Caller.KeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs wordOf Wit)
open VerifiableInference.Desc.Sound (Frame Piece below strsOf colAt behind wordsOf wordAt msgsOf
  MsgT)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)

variable {F : Frame} {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Xi : Type} (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (n0 : ℕ)
  (b₀ : TB (Letters.plain r H) iJ iQ)

/-- The reading of a statement behind, by make. -/
noncomputable abbrev fbMade (b : Rec × F.E.Str) : TB (Letters.plain r H) iJ iQ :=
  fbOf (Letters.plain r H) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat)
    (fun _ => ((), ())) b

/-- **The promise behind is `Sig.CF` of the new members.** -/
theorem pb_iff_cf (b : Rec × F.E.Str) :
    lawPb (Letters.plain r H) iJ iQ (fbMade iJ iQ G seat n0 b₀ b) ↔
      (sigOf r.cs r.l).CF (fun o => newSmp n0 b.1 o) (wordsOf G r.cs r.l seat (strsOf F b.2)) :=
  ⟨fun h o => h.1 (.inr o), fun h => ⟨fun i => match i with
    | .inl i => ((plain_empty iJ iQ).false i).elim
    | .inr o => h o, trivial⟩⟩

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT)

/-- **The witness behind, made of a witness of the table of joints.** -/
noncomputable def wtMade :
    (Cb.Pv.SendLoc.loc (selZ (Letters.plain r H) iJ iQ).sw).tgt.W :=
  ((selZ (Letters.plain r H) iJ iQ).sw.S₀.join (selZ (Letters.plain r H) iJ iQ).sw.d.N
      (T := OMsg.Wit) (fun i => isEmptyElim i)
      (fun o => (msgsOf r.cs r.l seat arr w o, fun _ => 0)), ())

/-- **The first clause of what stands behind: each new member decodes to the witness's message.** -/
theorem rb_decs_iff (b : Rec × F.E.Str) :
    (∀ i, (selLoc (Letters.plain r H) iJ iQ).S.decs (fbMade iJ iQ G seat n0 b₀ b).1.2
        (fbMade iJ iQ G seat n0 b₀ b).2.1.2 i = some ((wtMade iJ iQ seat arr w).1 i).1) ↔
      ∀ o, (sigOf r.cs r.l).decs (fun o => newSmp n0 b.1 o)
        (wordsOf G r.cs r.l seat (strsOf F b.2)) o = some (msgsOf r.cs r.l seat arr w o) :=
  ⟨fun h o => h (.inr o), fun h i => match i with
    | .inl i => ((plain_empty iJ iQ).false i).elim
    | .inr o => h o⟩

/-- The third clause holds: the carried base joint asks nothing. -/
theorem rb_carried (b : Rec × F.E.Str) :
    (selLoc (Letters.plain r H) iJ iQ).A₁.relR
      ((fbMade iJ iQ G seat n0 b₀ b).1.1.2, (fbMade iJ iQ G seat n0 b₀ b).2.1.1)
      ((selLoc (Letters.plain r H) iJ iQ).S.msgs (wtMade iJ iQ seat arr w).1,
        (wtMade iJ iQ seat arr w).2) := trivial

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pb_iff_cf
#print axioms VerifiableInference.Desc.First.K2Caller.rb_decs_iff
#print axioms VerifiableInference.Desc.First.K2Caller.rb_carried
