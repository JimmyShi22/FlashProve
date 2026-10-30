-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/BigThrough.lean: restates the facts of Johnson/Flat/BigIns.lean for any type Q of
requests that maps into the instances by a function val, such as the subtype of instances that the
program's reader accepts. What is assumed of Q, five things: its block (eB), its fixed instance
(ez), its early part (eE) and its reading of the request's item (eS: sp is `reqX` through val) are
those of Johnson/Flat/BigIns.lean, read through val; and where its reader insQ returns a member q,
`insOf P` returns val q (hins: a law on Q's own reader, one way). Nothing else is asked of Q: the
facts hold at every Q for which these five are shown; none is shown here.

  `insSub p`: reads a user's statement as a member of the subtype of instances that satisfy p: it is
    `insOf P`, and returns nothing where p fails. `insSub_some`: what it returns is what `insOf P`
    returns. `insSub_port`: it returns for an accepted call (`K.PortYesAt`: the yes of the program's
    checks, not the exit code) whose parameter file gives the sizes P (`sizesAt F.pol = .ok P`), if
    p holds of every instance with r < e (and y = 0 if e is before the window's end).
  `hblk_through`, `hitm_through`: `block_of_ins` and `item_of_ins`
    (Johnson/Maker/Page/CallInstAt.lean), read through val, at Q: two sentences "at every served
    call that the program accepts and at which insQ returns a member": the block at the call's
    member is the program's block; `reqX` at its early part is the program's item.
    No statement of the library
    takes either as a premise in this form.




Assumes also: `0 < P.V`, `sizesAt Z.pol = .ok P`, `planOf Z = .ok pl`; and, for `hblk_through` and
`hitm_through`, that a served statement has Z's three public files (hSv). At a Z whose acceptance
policy is not exact match no P meets the second, and the two laws say nothing, also of calls that
the program accepts.

Limits: those of Johnson/Flat/BigIns.lean's head.
The two laws are used at the full size alone
(Johnson/Flat/BigReqAt.lean); `insSub`, `insSub_some` and `insSub_port` are used by no other file.
One direction only: from an accepted call to the equations. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.BigIns

set_option autoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Maker OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify

variable {P : Params}

/-- **The reading of a user's statement as a member of a sub-type of the instances.** -/
def insSub (p : Instance' P → Prop) [DecidablePred p] (x : K.UserStm) : Option {i : Instance' P // p
  i} :=
  (insOf P x).bind fun i => if h : p i then some ⟨i, h⟩ else none

/-- What it returns is what `insOf P` returns. -/
theorem insSub_some {p : Instance' P → Prop} [DecidablePred p] {x : K.UserStm}
    {q : {i : Instance' P // p i}} (h : insSub p x = some q) : insOf P x = some q.val := by
  unfold insSub at h
  cases hi : insOf P x with
  | none =>
    rw [hi] at h
    cases h
  | some i =>
    rw [hi] at h
    have h' : (if hp : p i then some (⟨i, hp⟩ : {i : Instance' P // p i}) else none) = some q := h
    split at h'
    · cases h'
      rfl
    · cases h'

/-- **At the program's yes it returns**, where `sizesAt` reads P off the call's parameter file and p
holds of every instance with r < e (and y = 0 if e is before the window's end). -/
theorem insSub_port {p : Instance' P → Prop} [DecidablePred p]
    (hp : ∀ i : Instance' P, i.r < i.e → (i.e < P.T → i.y.val = 0) → p i) {F : K.Files}
    {id : String} {table further : OnBytes.Params.TableName}
    (h : K.PortYesAt F id table further) (o : Options) (hP : sizesAt F.pol = .ok P) :
    ∃ q, insSub p (K.stmOf F o) = some q := by
  obtain ⟨_, i, _, _, _, hi, _, _, hre, hy⟩ := insOf_port h o hP
  refine ⟨⟨i, hp i hre hy⟩, ?_⟩
  unfold insSub
  rw [hi]
  exact dif_pos (hp i hre hy)

section Through
variable (hV : 0 < P.V) {pl : Planned} {Z : K.Pub} (hP : sizesAt Z.pol = .ok P)
  (hpl : planOf Z = .ok pl) {Q : Type} (val : Q → Instance' P) (insQ : K.UserStm → Option Q)
  (hins : ∀ x q, insQ x = some q → insOf P x = some (val q))
  (Sv : K.UserStm → Prop) (hSv : ∀ x, Sv x → x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL)

include hP hpl hins hSv in
/-- **The block at the member of an accepted call whose statement meets Sv (its three public files
are Z's) is the program's block**, at Q. -/
theorem hblk_through (blk : Q → Blk Proof.FirstEnd)
    (eB : ∀ q, blk q = (pubOf pl P hV).block (val q)) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (q : Q) (pl' : Planned) (so : Head.StOwn) (cov : Head.Covered)
      (links : Array Stages.LinkH),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insQ (K.stmOf F o) = some q →
      planned F.pol F.KL (some F.lay) = .ok pl' →
      Head.stFromCall (words32 F.request) (words32 F.y) pl'.X.T = .ok so →
      Head.coveredOf so pl'.X.T pl'.X.P.h.V = .ok cov → linksOf pl'.X cov = .ok links →
      blk q = blockAt pl' links so.y := by
  intro F o id table further q pl' so cov links h hs hi hp' hso hcov hl
  rw [eB]
  exact block_of_ins hV Z.pol Z.lay Z.KL hP hpl Sv hSv _ rfl F o id table further (val q) pl' so
    cov links h hs (hins _ _ hi) hp' hso hcov hl

include hP hpl hins hSv in
/-- **The item read off the early part of the member of such a call is the program's item**, at Q.
-/
theorem hitm_through (sp : Q → ByteArray)
    (eS : ∀ q, sp q = (holdsIns hV Z.pol Z.lay Z.KL).reqX (val q)) (ear : Q → Q)
    (eE : ∀ q, val (ear q) = withoutReply hV (val q)) :
    ∀ (F : K.Files) (o : Options) (id : String) (table further : OnBytes.Params.TableName)
      (q : Q) (item : ByteArray),
      K.PortYesAt F id table further → Sv (K.stmOf F o) → insQ (K.stmOf F o) = some q →
      Proof.requestItem F.pol F.KL F.request = some item → sp (ear q) = item := by
  intro F o id table further q item h hs hi hit
  rw [eS, eE]
  exact item_of_ins hV Z.pol Z.lay Z.KL hP hpl Sv hSv _ rfl _ rfl F o id table further (val q)
    item h hs (hins _ _ hi) hit

end Through

end Johnson.Session
