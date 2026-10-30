-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/StringsNew.lean: code switching (the kind K2): «SHOWN» AND «NO COLLISION»,
AS THE TABLE OF JOINTS' PROMISE ASKS THEM (shownJT · noCollJT,
Johnson/Desc/Sound/MeaningSig.lean), AT THE TENANTS OF A NEW SENDING, from the library's own
condition Sig.CF and «every leaf is shown» at that sending's typed members. For the tie t2. NO
BLOCK IMPORTS THIS FILE.
Asking that the typed members BE members of the table's list
(literal membership and an equation of sendings, which hold a function) and that the table's reader
of OOD samples give the typed sample TO THE SEED would ask
more than the proofs need and may be unpayable at the closed list of members, where both seeds are
chosen. HERE: members are ALIKE (Alike, PinMove.lean: one shape and radius, one seat), and the
samples agree UP TO THE SEED's VALUES. ms: the table's list of all sendings' members. sM: the one
sending, typed. X: the tenants spoken of (at a switch into group m: N.sent m 0).
  MembersLike ms sM X   THE TIE BETWEEN THE TABLE's MEMBERS AND THE SENDING, AS A NAMED PREMISE,
                        four clauses on lists: onto (every tenant of X is a typed member's seat) ·
                        into (every typed member's seat is a tenant of X) · sits (at each tenant
                        of X a member of ms sits) · like (whoever of ms sits at the typed member
                        i's seat is alike to it)
  SmpLike smp a sM σ    the table's reader gives, at each typed member, a sample with σ's answers
                        and a seed that has σ's seed's values
  cf_at_typed   CfAt at a typed member, from SmpLike, «shown» and Sig.CF σ (clash_congr)
  sn_new        MembersLike · SmpBySeat · SmpLike · every leaf of each typed member is
                shown · Sig.CF σ at the typed members' words: at every tenant of X: shownJT and
                noCollJT (shown_move · cf_move)
  k2_sn_new     the same with Sig.CF drawn from the switch's law's own promise behind (lawPb at
                fbMade; pb_iff_cf, Johnson/Top/H0/K2Caller/BehindSig.lean), at sM := ⟨r.l, seat⟩
                and σ := newSmp n0 b.1
LIMITS. MembersLike · SmpBySeat · SmpLike · «every leaf is shown» are premises (the last:
shownBehind, Johnson/Desc/Sound/ShownBehind.lean). No soundness is claimed.
-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Sound.PinMove
import Johnson.Top.H0.K2Caller.BehindSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound

/-- The table's members at the tenants X are alike to the sending sM's. -/
structure MembersLike (ms : List Mem) (sM : Sending) (X : List (ℕ × ℕ)) : Prop where
  onto : ∀ x ∈ X, ∃ i, sM.seat i = x
  into : ∀ i, sM.seat i ∈ X
  sits : ∀ x ∈ X, ∃ e ∈ ms, SitsAt e x.1 x.2
  like : ∀ i, ∀ e ∈ ms, SitsAt e (sM.seat i).1 (sM.seat i).2 → Alike e ⟨sM, i⟩

/-- The table's reader gives σ at sM's members, up to the seed's values. -/
def SmpLike {A : Type} (cs : OnBytes.Codes)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (a : A)
    (sM : Sending) (σ : (sigOf cs sM.l).Smp) : Prop :=
  ∀ i, ∃ zz, smp a sM i = some zz ∧
    ((sigOf cs sM.l).om i).Z.val zz.1 = ((sigOf cs sM.l).om i).Z.val (σ i).1 ∧ zz.2 = (σ i).2

theorem cf_at_typed {A Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    {sM : Sending} (a : A) (y : Strs) (σ : (sigOf cs sM.l).Smp) (hσ : SmpLike cs smp a sM σ)
    (hsh : ∀ i, ShownAt G cs sM.l sM.seat y i)
    (hcf : (sigOf cs sM.l).CF σ (wordsOf G cs sM.l sM.seat y)) (i : Fin sM.l.length) :
    CfAt G cs sM.l sM.seat (fun z => smp z sM) i a y := by
  obtain ⟨zz, hz, hv, -⟩ := hσ i
  exact ⟨zz, hz, hsh i, fun hc => hcf i ((clash_congr _ _ zz.1 (σ i).1 hv).1 hc)⟩

theorem sn_new {A Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    {ms : List Mem} {sM : Sending} {X : List (ℕ × ℕ)} (M : MembersLike ms sM X)
    (hBy : SmpBySeat cs smp) (a : A) (y : Strs) (σ : (sigOf cs sM.l).Smp)
    (hσ : SmpLike cs smp a sM σ) (hsh : ∀ i, ShownAt G cs sM.l sM.seat y i)
    (hcf : (sigOf cs sM.l).CF σ (wordsOf G cs sM.l sM.seat y)) :
    ∀ x ∈ X, shownJT cs G ms x.1 x.2 y ∧ noCollJT cs G smp ms x.1 x.2 a y := by
  intro x hx
  obtain ⟨i, rfl⟩ := M.onto x hx
  refine ⟨⟨M.sits _ hx, fun e he hse => ?_⟩, fun e he hse => ?_⟩
  · exact (shown_move cs G e ⟨sM, i⟩ (M.like i e he hse) y).2 (hsh i)
  · exact (cf_move cs G smp e ⟨sM, i⟩ (M.like i e he hse) a (hBy a e ⟨sM, i⟩ (M.like i e he hse))
      y).2 (cf_at_typed cs G smp a y σ hσ hsh hcf i)

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (MembersLike SmpLike sn_new)

variable {F : Frame} {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Xi : Type} (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (n0 : ℕ)
  (b₀ : TB (Letters.plain r H) iJ iQ)

theorem k2_sn_new {A : Type}
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    {ms : List Mem} {X : List (ℕ × ℕ)} (M : MembersLike ms ⟨r.l, seat⟩ X)
    (hBy : SmpBySeat r.cs smp) (a : A) (b : Rec × F.E.Str)
    (hσ : SmpLike r.cs smp a ⟨r.l, seat⟩ (fun o => newSmp n0 b.1 o))
    (hsh : ∀ i, ShownAt G r.cs r.l seat (strsOf F b.2) i)
    (hb : lawPb (Letters.plain r H) iJ iQ (fbMade iJ iQ G seat n0 b₀ b)) :
    ∀ x ∈ X, shownJT r.cs G ms x.1 x.2 (strsOf F b.2) ∧
      noCollJT r.cs G smp ms x.1 x.2 a (strsOf F b.2) :=
  sn_new r.cs G smp M hBy a (strsOf F b.2) (fun o => newSmp n0 b.1 o) hσ hsh
    ((pb_iff_cf iJ iQ G seat n0 b₀ b).1 hb)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2.cf_at_typed
#print axioms VerifiableInference.Desc.First.K2.sn_new
#print axioms VerifiableInference.Desc.First.K2Caller.k2_sn_new
