-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkList.lean: ALL THAT IS LEFT OF `ThreeAsksR` (ThreeTiedR.lean: the
three laws of a link's pieces and five ties a piece) AT THE COMPOSED MEANING (`mgAll 𝔇 mgBase`:
over the closed base), AS ONE NAMED LIST: `LinkList`. IT TAKES THE PLACE OF THE THREE LISTS
LinkDebts · LinkLeft · LinkLeftRw: one structure, one theorem, written by one program, which lays
each payer in as it comes. The payers that are laid in: the law with the two sentences on worths
(`link_table_worth_left`, WorthLeft.lean); the ties (TiesAtMg.lean; `t4_batch`, `t3_eq_all`,
`step_of_out`, `ahead_none`, `full_of_facts`, `t5b_list`, `t5q_list`, `t5e_list`); the law's three
premises on the public sentence (`rwAt_hR1`, `rwAt_hR2`, `rwAt_hR3_reached`); the closed facts on
the written list (K09Rows.lean, K09Open.lean, K09Places.lean, K09More.lean); the hand-on of the
promise over the batching (' + bt + 'h01_mgR' + bt + ', RidesAtMgR.lean).

What is said.
  `totalIn_some`: where the one sum can be taken a part is there. `LinkList 𝔇 mgBase links pl z Rz
    k m …`: at the public part z, at the link of number m whose batching stands at border k: 45
    named fields. `threeAsksR_of_list`: **`ThreeAsksR 𝔇.N (mgAll 𝔇 mgBase) links pl Rz k pb pq pe
    relFW relTotB relTotB' relTot relRow z` from it**, where k is the number of the batching in the
    written list, the six Bools on the list say yes, the written list is the full one, AND THE FACTS
    ON THE SEAT HOLD (premises of the theorem, not fields of the list: the link has its sort and its
    ties (`SegAt`); the composed meaning's link of that number is the link; the three pieces hold
    the link's two own sub-protocols and one whose yes is the one equation's; these stand at their
    numbers of the list along which «reached» runs; they are rows of moves; the three extractors lay
    nothing; «reached» is handed on over the batching's piece and is reached along that list; the
    committed table's decoder answers alike at any two states).

Limits. BOOK-KEEPING: THE LIST IS THE DEBT: nothing of it is paid here; that its fields can be met
together is shown nowhere. The law's letter C is fixed at «the rows fit» (`rowsFit p.rows π`): the
fields that name it are asked there. Every field on a state is asked only inside `onTR` (the table's
promise, no mark, reached), but those of the law's own premises that speak of the runs' texts or of
the letters. NO FIELD IS A TIE OR A LAW OF A PIECE ANY MORE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WorthLeft
import Johnson.Desc.First.Link.Law.TiesAtMg
import Johnson.Desc.First.Link.Law.TieFourBatch
import Johnson.Desc.First.Link.Law.TieThreeAll
import Johnson.Desc.First.Link.Law.FifthTieList
import Johnson.Desc.First.Link.Law.TieFronts
import Johnson.Desc.First.Link.Law.RwAtReached
import Johnson.Desc.First.Link.Law.K09Rows
import Johnson.Desc.First.Link.Law.K09Open
import Johnson.Desc.First.Link.Law.K09Places
import Johnson.Desc.First.Link.Law.K09More
import Johnson.Desc.First.Link.Law.ShutList

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

/-- Where the one sum can be taken a part is there. -/
theorem totalIn_some (own : List (ℕ × ℕ)) (s : S) (h : K9.totalIn own s = true) :
    (atS.get? s).isSome = true := by
  unfold K9.totalIn at h
  cases e : atS.get? s with
  | none => rw [e] at h; exact absurd h Bool.false_ne_true
  | some _ => rfl

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

/-- **ALL THAT IS LEFT OF THE THREE LAWS AND THE FIFTEEN TIES OF ONE LINK, AT THE PUBLIC PART
z.** sT: the digits' seats at the composed meaning's data. -/
structure LinkList (α : Type) (sub : First.ModelPart) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (o : ℕ × String) (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (fd : FoldData) (reqW : P → Array UInt32) : Prop where
  /-- THE LAW's OWN PREMISES (link_table_worth_left), to the letter, the letters laid
  in; its letter C at «the rows fit» -/
  A : LinkOwes sub L φ (fun q => Ok q ∧ (rowsFit p.rows π) q) (FullAt nU) p pw tmOf lenOf d N b₃ pb
    pq pe (fun a => (o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows π) (fixed9 φ a.1)) o1 o2 o3 (fun a w
    => tabAt own (rdW w) a.1) cx
  /-- of the law's premise T (TableOwes) the three fields that are left -/
  hbook₂ : ∀ m ∈ (moves₂ (α := α) L).map (·.move), MoveBook m
  htin : ∀ a t, o1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] → K9.totalIn own t =
    true
  hitems : ∀ a w, o0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read) (rs : List (TermedRun S (α ×
    Option Pub9) GQ × (α × Option Pub9 → Bound GQ → List GQ))), atS.get? a.1 = some b ∧ (∀ x ∈ rs,
    x.1 ∈ rlOf L tmOf lenOf ∧ ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
    (𝔇.Rd m).forms e.1 e.2 a.1 = some R ∧ K9.formsIn (𝔇.Rd m) own e.1 e.2 a.1 = true ∧ ∀ f ∈
    R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈ rs.flatMap fun x => x.2
    (fixed9 φ a.1) (dataQ own b (rdW w))
  hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)
  hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl → φ ((s.putTl tl').putFork F1) =
    φ s
  hOk4 : ∀ q v tlb g, (Ok q ∧ (rowsFit p.rows π) q) → q.2 = some v → (π q.1).1 = some tlb →
    tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList, K4Values.InWin
    (winOf g.leaves) x.1 ∨ Filled v.F x.1
  ho : o ∈ L.order
  hAt : At L o run
  hu : Under run k8Run.2
  ht : tmOf o = fun n q y => numbered n (vals4 π (ent4 π) q y) ++ tmRest π q y
  HD : DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp
  okDig : ∀ q tlb v, (Ok q ∧ (rowsFit p.rows π) q) → (π q.1).1 = some tlb → q.2 = some v → DigStatic
    tlD tlb v.F
  okEnts : ∀ q tlb g, (Ok q ∧ (rowsFit p.rows π) q) → (π q.1).1 = some tlb → tlb.heard = some g → ∀
    cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row
  hLeft : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := α) L).map (·.move)) b'.1 = .ok t → atS.get? t
    = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard = some g →
    b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs → blank u tl
    = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c)
    → Fx9 φ (fun q => Ok q ∧ (rowsFit p.rows π) q) (fixed9 φ a.1) e → Fx9 φ (fun q => Ok q ∧
    (rowsFit p.rows π) q) (fixed9 φ a.1) t → laterK atS (O9 (K := GE8) φ (fun q => Ok q ∧ (rowsFit
    p.rows π) q) (FullAt nU)) ((e.putTl tl').putFork F1) t → DigitsLeft x tlD 𝔇.sent 𝔇.l3.rad sT
    𝔇.l3.arr (pb.ext a τ w₀) g tl c b.L y
  /-- IN THE PLACE OF THE LAW's THREE PREMISES ON THE PUBLIC SENTENCE: the composed meaning's test
  is the batching kind's own test on the rows -/
  hrw : ∀ s, 𝔇.rw m s = K9.rowsFit p.rows s
  /-- the runs' share of the link -/
  share : LinkShare L p
  /-- the two sub-protocols' moves leave the numbers; the runs stand -/
  numB : ∀ mv ∈ ([.add (claimsInBy L.each L.hear L.order)] : List (Move S)), MoveNum u mv
  numQ : ∀ mv ∈ ([.quiet L.runBehind] : List (Move S)), MoveNum u mv
  /-- IN THE PLACE OF THE LAW's PREMISE h01 (the promise is handed on over the batching): the plan's
  numbers of trees and of messages stand still over the place; what the four riders on the oracles
  take, inside onTR -/
  treesB : 𝔇.N.treesAt pl[k + 1]? = 𝔇.N.treesAt pl[k]?
  msgsB : 𝔇.N.msgsAt pl[k + 1]? = 𝔇.N.msgsAt pl[k]?
  oraB : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b → OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links
    pl z k pb.base a.1 b.1
  /-- THE TIES' PREMISES. Closed facts on the plan: the digits' place; the listed runs hold the
  rows' runs; a row is due -/
  hpc : 7 + shift sub = Desc.K3.pieceAt X m true
  hdig : digAt X m = some (x, tlD)
  hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items
  hn : 0 < (𝔇.N.rowsAt m .equation).2
  /-- ON STATES, EACH ASKED ONLY INSIDE onTR: every entry that the open segment's data read lies
  inside the ranges of the member at its seat: in front of the batching; behind the runs behind it;
  in front of the one equation -/
  inSeg : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x
  inRun : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a → InsideAt
    𝔇.cs 𝔇.ms own a
  inTot : ∀ b, onK (k + 1 + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a
  /-- THE FACTS ALONG THE FOLD (FoldFacts), AT THE LIST's OWN «reached»: one field
  for all that is drawn from them; with two facts that tie their data to the plan: the link's
  messages are no more than its own list holds; the group's number is the plan's -/
  FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) fd reqW links pl
  hall : ∀ ms, (fd.sent.shape.link[m]?).map (·.messages) = some ms → ms.length ≤ (fd.ownAt m 3).size
  hgr : fd.groupAt m = 𝔇.N.groupAt m
  /-- what the pins' ride backward asks -/
  pinB : ∀ a τ b, onK k a → pb.ior.red.out a τ = some b → PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pb.base a.1
    b.1
  pinQ : ∀ a τ b, onK (k + 1) a → pq.ior.red.out a τ = some b → PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m
    pq.base a.1 b.1
  /-- closed: the members that the last row can weigh are there, with the plan's shapes; three facts
  that tie the fold's data to the plan; on the plan's numbers: behind the equation just the rows up
  to its own are due -/
  hmem : membersThereB fd 𝔇.ms own (𝔇.N.msgsAt pl[k + 1 + 1 + 1]?) = true
  hcs : fd.sent.codes = 𝔇.cs
  hft : fd.ft = 0
  hN : fd.M.length ≤ N
  hdue : rowsDue 𝔇.N ((openSets links pl (First.start links))[k + 1 + 1 + 1]?.getD []) m =
    (𝔇.N.rowsAt m .equation).1 + 1
  /-- in front of the one equation the one sum can be taken -/
  tot : ∀ a, onK (k + 1 + 1) a → K9.totalIn own a.1 = true
  /-- WHAT THE FIFTH TIE AT THE THREE PIECES TAKES: on the composed meaning's data alone: it is the
  meant one; its head's part is the head kind's, whose request's reader reads the public part alone
  and whose token's reader the heard reply alone -/
  mh : MeantHead 𝔇
  /-- a test with code a piece: the riders lie low -/
  lowB : lowAtB 𝔇.N pb.base k = true
  lowQ : lowAtB 𝔇.N pq.base (k + 1) = true
  lowE : lowAtB 𝔇.N pe.base (k + 1 + 1) = true
  /-- on states, inside onTR: in front of the one equation no message of the link's own is the index
  masks' message -/
  notIx : ∀ a, onK (k + 1 + 1) a → OwnNotIndex a.1

/-- **THE THREE LAWS AND FIVE TIES A PIECE, FROM THE ONE LIST.** -/
theorem threeAsksR_of_list (hk : k = batchAt links pl m) (hfit : rows9Fit links pl = true)
    (hof : rowOpenFit links pl = true) (hpf : placesFit links pl = true) (hm : m < 25)
    (hlinks : links = linksFull) (hpl : pl = plF) (hkx : k = batchIx m)
    (hlf : linkFit links pl = true) (hp9 : pubFit9 true moreAll links pl = true)
    (hmf : moreFit links pl = true)
    (α : Type) (sub : First.ModelPart) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (o : ℕ × String) (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (fd : FoldData) (reqW : P → Array UInt32)
    (hs : links[m]? = some sub) (eb : ∀ a τ w, pb.ext a τ w = w) (eq : ∀ a τ w, pq.ext a τ w = w)
    (ee : ∀ a τ w, pe.ext a τ w = w) (he : pe.b = below b₃) (hpb : pb.b = below L.batchB)
    (hpq : pq.b = below L.behindB) (seg : SegAt m sub L) (lk : 𝔇.lk m = some L)
    (atK : bs[k]? = some L.batchB) (atK1 : bs[k + 1]? = some L.behindB)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (movesQ : IsMoves atS [.quiet L.runBehind] L.behindB)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (handB : HandsOn Rz k pb) (rchIs : ∀ j a, Rz j a → Reach ft bs st0 j (z, a.1))
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (H : LinkList 𝔇 links pl z Rz k m α sub L φ Ok nU p pw tmOf lenOf d N b₃ pb pq pe items u π
      o run x tlD set pp (fun j => 𝔇.l3.seat x.link true j.1) ft bs st0 fd reqW) :
    ThreeAsksR 𝔇.N Mg links pl Rz k pb pq pe
      (relFW (𝔇.Rd m) own rdW items forkR heardD x tlD 𝔇.sent 𝔇.l3.rad
        (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr)
      (relTotB α L own rdW (rwAt 𝔇 m) cx) (relTotB' α L own rdW (rwAt 𝔇 m))
      (relTot own rdW (rwAt 𝔇 m)) (relRow own N rdW) z := by
  have R := rows9_at links pl hfit m sub hs
  have hop := rowOpen_at links pl hof m (List.getElem?_eq_some_iff.1 hs).1
  obtain ⟨p0, hp0, hl0, h7, h11⟩ := place_batch links pl hpf m (List.getElem?_eq_some_iff.1 hs).1
  obtain ⟨p2, hp2, hl2⟩ := place_eq links pl hpf m (List.getElem?_eq_some_iff.1 hs).1
  obtain ⟨pB, pB1, hpB, hpB1, hlB, hpcB⟩ :=
    more_batch links pl hmf m (List.getElem?_eq_some_iff.1 hs).1
  rw [← hk] at R hop hp0 hp2 hpB hpB1
  obtain ⟨seats, r, hM⟩ := H.mh.meant
  obtain ⟨cs, arr, msR, Nh, sz, seat, plh, tab, put, Hh, tokH, h𝔇, hreq, htok⟩ := H.mh.headIs
  have g := link_table_worth_left (rowsFit p.rows π) (rwAt 𝔇 m) m sub L seg φ Ok nU p pw tmOf
    lenOf d N b₃ pb pq pe o0 o1 o2 o3 cx (𝔇.Rd m) own rdW items H.A
    ⟨fun c hc => totalIn_some own c.1 (H.tot c hc), H.hbook₂, H.htin, H.hitems⟩
    (h01_mgR 𝔇 𝔇.N links pl z Rz k m pB pB1 hlf hp9 hpB hpB1 hlB hpcB H.treesB H.msgsB L p H.share
      pb hpb handB H.oraB)
    (fun a τ b' _ h =>
      rwAt_hR1 𝔇 m u φ π H.hπ p H.hrw _ L.batchB drawB H.numB pb hpb a τ b' h)
    (fun a τ b' _ h =>
      rwAt_hR2 𝔇 m u p.rows H.hrw _ L.behindB movesQ H.numQ pq hpq a τ b' h)
    (rwAt_hR3_reached 𝔇 mgBase links pl z Rz k m u L p pw H.share.two H.hrw atK atK1 (rchIs _) b₃
      hb₃ pe he)
    u π H.hπ H.hkeep H.hOk4 o H.ho run H.hAt H.hu H.ht forkR heardD x tlD 𝔇.sent 𝔇.l3.rad
    (fun j => 𝔇.l3.seat x.link true j.1) 𝔇.l3.arr H.HD (fun _ => rfl) (fun _ => rfl) H.okDig
    H.okEnts H.hLeft
  exact ⟨g.1, g.2.1, g.2.2,
    tb_of 𝔇 mgBase links pl z Rz k m α L p lk H.share.two R.1.2.1 R.1.2.2 H.inRun pb hpb hd _
      (t4_batch 𝔇 mgBase links pl z Rz k m sub items x tlD R.1.1 R.1.2.2 H.hpc H.hdig H.hruns
        H.inSeg (fun a ha y hy => ahead_none (𝔇.N.sent m) own y
          (full_of_facts 𝔇 mgBase links pl z Rz k m H.FF p0 hp0 hl0 h7 h11 H.hall a ha y hy)) pb eb
        H.pinB)
      (t5b_list 𝔇 mgBase links pl z Rz k m hm hlinks hpl hkx L p drawB H.share.stand pb hpb eb hM
        h𝔇 hreq htok H.lowB),
    tq_of 𝔇 mgBase links pl z Rz (k + 1) m α L p lk H.share.two R.2.1.1 R.2.1.2.1 R.2.1.2.2 H.inRun
      H.inTot pq hpq eq H.pinQ hd
      (t5q_list 𝔇 mgBase links pl z Rz k m hm hlinks hpl hkx L p drawB H.share.stand pq hpq eq hM
        h𝔇 hreq htok H.lowQ),
    te_of 𝔇 mgBase links pl z Rz (k + 1 + 1) m N pw b₃ hb₃ R.2.2.1 R.2.2.2.2 H.inTot pe he ee hd
      (t3_eq_all 𝔇 mgBase links pl z Rz (k + 1 + 1) m H.FF N R.2.2.2.1 H.hn hop H.hdue p2 hp2 hl2
        H.hgr H.hcs H.hft H.hN H.hmem H.tot H.inTot pe
        fun a τ b _ h => step_of_out pw b₃ hb₃ pe he a τ b h)
      (t5e_list 𝔇 mgBase links pl z Rz k m hm hlinks hpl hkx pw b₃ hb₃ pe he ee hM h𝔇 hreq htok
        H.lowE H.notIx)⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.totalIn_some
#print axioms VerifiableInference.Desc.LinkJoin.threeAsksR_of_list
