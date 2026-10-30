-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkRestC.lean: ON THE SECOND ROAD (the law's letter C at `rowsLen`):
BENEATH THE SECOND LIST OF WHAT IS LEFT AT A LINK's THREE PIECES (`LinkListC`, LinkListC.lean): THE
SAME LIST, ITS FIELD A (`LinkOwes`: eight lists of debts) CUT INTO ITS PARTS (the names that begin
with A, but AreadyS, which is the list's own; of A's «ready» nothing is left: it follows from
AreadyS), LESS THE FIELDS THAT HAVE A PAYER AT THE CLOSED CONSTANT: Ablocks, Ahpb, Ahpq, Ahpe,
Acaller, Ah01, Ah12, Ahon3, Aletters, htin, hrw, treesB, msgsB, oraB, hpc, hn, FF, hall, hgr, pinB,
pinQ, hcs, hft, hdue, lowB, lowQ, lowE. A structure (cut by program out of `LinkListC`'s own text)
and one theorem.

What is said.
  `LinkRestC …`: the 37 fields that are left, each to the letter as in `LinkListC`.
    `linkListC_of_rest`: **`LinkListC` from `LinkRestC` and the 27 paid fields** (premises of the
    theorem, each in its field's own type).

Limits. BOOK-KEEPING. `LinkRestC` IS THE DEBT. THE COMMENTS OVER THE FIELDS ARE THE LIST's OWN,
GROUP BY GROUP, UNTURNED: where a group's comment names a fact that is paid (Ablocks, Ahpb, Ahpq,
Ahpe, Acaller, Ah01, Ah12, Ahon3, Aletters, htin, hrw, treesB, msgsB, oraB, hpc, hn, FF, hall, hgr,
pinB, pinQ, hcs, hft, hdue, lowB, lowQ, lowE), that fact is no field here: it is a premise of the
theorem. The count of fields is no measure. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkListC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (Where atS segAt?)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf formsOf shift openSets
  rowsDue FoldFacts FoldData)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)
open Johnson.Desc.First.Walk.Tied (Reach MeantAt)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Sound.Frame}
  (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 mgBase
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "cx" => ctxPins 𝔇.N (mgAll 𝔇 mgBase) z m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz
local notation "o0" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz k
local notation "o1" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1)
local notation "o2" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1 + 1)
local notation "o3" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1 + 1 + 1)

/-- **THE LINK's LIST, LESS WHAT HAS A PAYER AT THE CLOSED CONSTANT.** -/
structure LinkRestC (α : Type) (sub : First.ModelPart) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (o : ℕ × String) (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (fd : FoldData) (reqW : P → Array UInt32) : Prop where
  /-- the first piece's one round -/
  Ahds : pb.ds = [k9Round p]
  /-- the first piece puts nothing back -/
  Ahbk : pb.back = []
  /-- THE KINDS' LAWS ON THEIR RUNS (the list «runs») -/
  Aruns : OwesRuns sub L φ (fun q => Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf
    lenOf))) q) (FullAt nU) tmOf lenOf
  /-- the numbers (the list «numbers») -/
  Anumbers : OwesNumbers L φ (fun q => Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf
    lenOf))) q) tmOf lenOf d
  /-- «full» (the list «full») -/
  Afull : OwesFull L (FullAt nU) tmOf lenOf
  /-- behind the batching a part is there -/
  Ahs1 : ∀ b, o1 b → (atS.get? b.1).isSome = true
  /-- at most N oracle messages -/
  AhN : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  /-- every block of a required array lies inside it -/
  Ainside : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r, reqArray a.L.check.rows.layout
    born name = some r → ∀ bl ∈ r.blocks, Inside r bl
  /-- NEW AGAINST THE ELDER LIST: WHAT THE SECOND HALF OF C TAKES, TO BE DRAWN FROM THE BATCHING
  PIECE's OWN YES: the promise Ok holds of the snapshot in front, UNDER «THE ROWS FIT» ALONE (not
  under the whole of C: at the place where it is called the second half is not yet in hand) -/
  AreadyS : ∀ a, ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows π) (fixed9 φ a.1)) → Ok (fixed9 φ a.1)
  /-- each run's law AT THE BARE PROMISE Ok (without C) -/
  hrunsB : ∀ r ∈ rlOf L tmOf lenOf, RunOk Reading.gl atS (O9 φ Ok (FullAt nU)) (Fx9 φ Ok) r.run.2
    r.tm r.len
  /-- the link's gatherer keeps the map of the claims' numbers, the plan's number and the count -/
  hk : KeepsKap atS (claimsInBy L.each L.hear L.order)
  /-- of the law's premise T (TableOwes) the three fields that are left -/
  hbook₂ : ∀ m ∈ (moves₂ (α := α) L).map (·.move), MoveBook m
  hitems : ∀ a w, o0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read) (rs : List (TermedRun S (α ×
    Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))), atS.get? a.1 = some b ∧ (∀ x ∈ rs,
    x.1 ∈ rlOf L tmOf lenOf ∧ ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
    (𝔇.Rd m).forms e.1 e.2 a.1 = some R ∧ K9.formsIn (𝔇.Rd m) own e.1 e.2 a.1 = true ∧ ∀ f ∈
    R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈ rs.flatMap fun x => x.2
    (fixed9 φ a.1) (dataQ own b (rdW w))
  hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)
  hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl → φ ((s.putTl tl').putFork F1) =
    φ s
  hOk4 : ∀ q v tlb g, (Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf))) q) → q.2 =
    some v → (π q.1).1 = some tlb → tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈
    cl.form.slots.toList, K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1
  ho : o ∈ L.order
  hAt : At L o run
  hu : Under run k8Run.2
  ht : tmOf o = fun n q y => numbered n (vals4 π (ent4 π) q y) ++ tmRest π q y
  HD : DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp
  okDig : ∀ q tlb v, (Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf))) q) → (π
    q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F
  okEnts : ∀ q tlb g, (Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf))) q) → (π
    q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb
    x.tree x.row
  hLeft : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t
    = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
    b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs → blank u tl
    = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c)
    → Fx9 φ (fun q => Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf))) q) (fixed9
    φ a.1) e → Fx9 φ (fun q => Ok q ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf))) q)
    (fixed9 φ a.1) t → laterK atS (O9 (K := GE8) φ (fun q => Ok q ∧ (rowsLen p.rows π (fun q =>
    lenRuns q (rlOf L tmOf lenOf))) q) (FullAt nU)) ((e.putTl tl').putFork F1) t → DigitsLeft x tlD
    𝔇.sent 𝔇.l3.rad sT 𝔇.l3.arr (pb.ext a τ w₀) g tl c b.L y
  /-- the runs' share of the link -/
  share : LinkShare L p
  /-- the two sub-protocols' moves leave the numbers; the runs stand -/
  numB : ∀ mv ∈ ([.add (claimsInBy L.each L.hear L.order)] : List (Move S)), MoveNum u mv
  numQ : ∀ mv ∈ ([.quiet L.runBehind] : List (Move S)), MoveNum u mv
  /-- IN THE PLACE OF THE LAW's PREMISE h01 (the promise is handed on over the batching): the plan's
  numbers of trees and of messages stand still over the place; what the four riders on the oracles
  take, inside onTR -/
  hdig : digAt X m = some (x, tlD)
  hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items
  /-- ON STATES, EACH ASKED ONLY INSIDE onTR: every entry that the open segment's data read lies
  inside the ranges of the member at its seat: in front of the batching; behind the runs behind it;
  in front of the one equation -/
  inSeg : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x
  inRun : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a → InsideAt
    𝔇.cs 𝔇.ms own a
  inTot : ∀ b, onK (k + 1 + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a
  /-- closed: the members that the last row can weigh are there, with the plan's shapes; three facts
  that tie the fold's data to the plan; on the plan's numbers: behind the equation just the rows up
  to its own are due -/
  hmem : membersThereB fd 𝔇.ms own (𝔇.N.msgsAt pl[k + 1 + 1 + 1]?) = true
  hN : fd.M.length ≤ N
  /-- in front of the one equation the one sum can be taken -/
  tot : ∀ a, onK (k + 1 + 1) a → K9.totalIn own a.1 = true
  /-- WHAT THE FIFTH TIE AT THE THREE PIECES TAKES: on the composed meaning's data alone: it is the
  meant one; its head's part is the head kind's, whose request's reader reads the public part alone
  and whose token's reader the heard reply alone -/
  mh : MeantHead 𝔇
  /-- on states, inside onTR: in front of the one equation no message of the link's own is the index
  masks' message -/
  notIx : ∀ a, onK (k + 1 + 1) a → OwnNotIndex a.1

/-- **THE LIST FROM THE REST.** -/
theorem linkListC_of_rest (α : Type) (sub : First.ModelPart) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (o : ℕ × String) (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (fd : FoldData) (reqW : P → Array UInt32)
    (Ablocks : OwesBlocks L p pw b₃)
    (Ahpb : pb.b = below L.batchB)
    (Ahpq : pq.b = below L.behindB)
    (Ahpe : pe.b = below b₃)
    (Acaller : OwesCaller pb pq pe)
    (Ah01 : ∀ a τ b', ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsLen p.rows π (fun q => lenRuns q (rlOf L
      tmOf lenOf))) (fixed9 φ a.1)) → pb.ior.red.out a τ = some b' → o1 b')
    (Ah12 : ∀ b τ c, o1 b → pq.ior.red.out b τ = some c → o2 c)
    (Ahon3 : ∀ c τ x, o2 c → pe.ior.red.out c τ = some x → o3 x)
    (Aletters : OwesLetters pb pq pe (fun a => (o0 a ∧ k9OnA a.1 = true) ∧ (rowsLen p.rows π (fun q
      => lenRuns q (rlOf L tmOf lenOf))) (fixed9 φ a.1)) o1 o2 (fun a w => tabAt own (rdW w) a.1)
      cx)
    (htin : ∀ a t, o1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] → K9.totalIn own
      t = true)
    (hrw : ∀ s, 𝔇.rw m s = K9.rowsFit p.rows s)
    (treesB : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?)
    (msgsB : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?)
    (oraB : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b → OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N
      links pl z k pb.base a.1 b.1)
    (hpc : 7 + shift sub = Desc.K3.pieceAt X m true)
    (hn : 0 < (𝔇.N.rowsAt m .equation).2)
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) fd reqW links pl)
    (hall : ∀ ms, (fd.sent.shape.link[m]?).map (·.messages) = some ms → ms.length ≤ (fd.ownAt m
      3).size)
    (hgr : fd.groupAt m = 𝔇.N.groupAt m)
    (pinB : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b → PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pb.base
      a.1 b.1)
    (pinQ : ∀ a τ b, onK (k + 1) a → pq.ior.red.out a τ = some b → PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m
      pq.base a.1 b.1)
    (hcs : fd.sent.codes = 𝔇.cs)
    (hft : fd.ft = 0)
    (hdue : rowsDue 𝔇.N ((openSets links pl (First.start links))[k + 1 + 1 + 1]?.getD []) m =
      (𝔇.N.rowsAt m .equation).1 + 1)
    (lowB : lowAtB 𝔇.N pb.base k = true)
    (lowQ : lowAtB 𝔇.N pq.base (k + 1) = true)
    (lowE : lowAtB 𝔇.N pe.base (k + 1 + 1) = true)
    (H : LinkRestC 𝔇 links pl z Rz k m α sub L φ Ok nU p pw tmOf lenOf d N b₃ pb pq pe items u π
      o run x tlD set pp sT ft bs st0 fd reqW) :
    LinkListC 𝔇 links pl z Rz k m α sub L φ Ok nU p pw tmOf lenOf d N b₃ pb pq pe items u π
      o run x tlD set pp sT ft bs st0 fd reqW :=
  ⟨⟨Ablocks, ⟨Ahpb, Ahpq, Ahpe, H.Ahds, H.Ahbk⟩, Acaller, H.Aruns, H.Anumbers, H.Afull, ⟨fun a ha =>
    ⟨ha.1.2, H.AreadyS a ⟨ha.1, rowsLen_rows ha.2⟩, ha.2⟩, Ah01, Ah12, H.Ahs1, H.AhN, H.Ainside,
    Ahon3⟩, Aletters⟩, H.AreadyS, H.hrunsB, H.hk, H.hbook₂, htin, H.hitems, H.hπ, H.hkeep, H.hOk4,
    H.ho, H.hAt, H.hu, H.ht, H.HD, H.okDig, H.okEnts, H.hLeft, hrw, H.share, H.numB, H.numQ, treesB,
    msgsB, oraB, hpc, H.hdig, H.hruns, hn, H.inSeg, H.inRun, H.inTot, FF, hall, hgr, pinB, pinQ,
    H.hmem, hcs, hft, H.hN, hdue, H.tot, H.mh, lowB, lowQ, lowE, H.notIx⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.linkListC_of_rest
