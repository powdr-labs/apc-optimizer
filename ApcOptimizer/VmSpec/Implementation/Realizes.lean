import ApcOptimizer.VmSpec.Implementation.Counting
import ApcOptimizer.VmSpec.Implementation.Rank

set_option autoImplicit false

/-! **What a host must be for its bus semantics to mean anything** — and the one thing that buys.

    `Spec.lean` treats `BusSemantics.accepts`/`maintainsInvariants` as opaque per-message
    predicates. `Host.realizes` says a concrete VM's own chips are what implement them. Every
    field is a property of the VM's fixed furniture — the `HostChip` predicates and `bs` — so it
    is checkable once per VM and holds for every optimizer run; nothing here mentions a guest
    circuit.

    What it buys is `Host.forcesAccepts`, which is **derived**, not assumed
    (`forcesAccepts_of_hostSound`): `VmSat` gives each guest instance only
    `Circuit.satisfiesAlgebraic`, whereas `Circuit.satisfies` also demands `accepts` on every
    active message, and the gap is closed by balancing.

    On stateless buses that is the manuscript's `bus_int.tex` induction: the host chips *are* the
    lookup tables, so a guest's active message has nowhere to go but into a chip that only
    receives table entries. On stateful buses the same shape gives the manuscript's
    `eq:legal:recv_byte` (`maintains_of_stateful_active`): a chip need only vouch for what it
    *sends*, and what it *receives* is vouched for by whoever sent the same tuple. Demanding the
    receive side per-chip would be assuming something false — a chip that reads memory does not
    constrain the value it finds there. That holds of the *host's* chips as much as a guest's,
    which is what `Host.statefulChipsMaintain` is shaped around. -/

variable {p : ℕ}

/-- The `GuestBusRules` a `BusSemantics` induces. **Internal**: the audited spec never uses this —
    a VM writes its rules out directly (`openVmGuestRules`) and proves them equal to this, which is
    what pins its `accepts` to the one `Circuit.satisfies` is stated against. Exactly three of
    `BusSemantics`'s four fields survive, and `maintainsInvariants` only up to the multiplicity.

    `r0` supplies the clock-facing fields (`execBusId`/`memBusId`/`getTimestamp`) that
    `BusSemantics` itself has no notion of — a template borrowed wholesale, since `Circuit.legalGuest`'s
    `sendOnly`/`polarity`/`size` never look at them, only `stepLayout` does. In practice `r0` is
    `openVmGuestRules`'s own value, so `openVmGuestRules_eq` gets them for free. -/
def BusSemantics.toGuestRules (bs : BusSemantics p) (r0 : GuestBusRules p)
    (hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩) :
    GuestBusRules p where
  isStateful := bs.isStateful
  accepts := bs.accepts
  payloadOk m := ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩
  execBusId := r0.execBusId
  memBusId := r0.memBusId
  getTimestamp := r0.getTimestamp
  memPayloadOnly := hmem

/-- On a stateful bus, acceptance follows from the payload being good — which is the contract
    `GuestBusRules.payloadOk` is named for, now stated directly rather than through a message whose
    multiplicity has to be quantified away.

    This is what lets a receive inherit its acceptance from whoever sent the same tuple. For
    OpenVM it holds by inspection: memory `accepts` asks that received data in a byte-checked
    address space be bytes, and memory `maintainsInvariants` asks exactly that of any message. -/
def BusSemantics.statefulAcceptsOfPayloadOk (bs : BusSemantics p) (r0 : GuestBusRules p)
    (hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩) : Prop :=
  ∀ msg : BusInteraction (ZMod p), bs.isStateful msg.busId = true →
    (bs.toGuestRules r0 hmem).payloadOk (msg.busId, msg.payload) → bs.accepts msg

/-- `Host.statefulChipsMaintain` still speaks of a whole message; this is the one-line bridge to
    `GuestBusRules.payloadOk`, which forgets its multiplicity. -/
theorem payloadOk_of_exists {bs : BusSemantics p} {r0 : GuestBusRules p}
    {hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩} {m : BusMessage p}
    (h : ∃ msg : BusInteraction (ZMod p), msg.busId = m.1 ∧ msg.payload = m.2 ∧
      bs.maintainsInvariants msg) : (bs.toGuestRules r0 hmem).payloadOk m := by
  obtain ⟨msg, h1, h2, h3⟩ := h
  exact ⟨msg.multiplicity, by cases msg; cases h1; cases h2; exact h3⟩

/-- The host's stateless chips are lookup tables: any stateless message they leave with a nonzero
    net multiplicity is one the semantics accepts. This is the manuscript's "table sink"
    (`bus_int.tex`), which implements its bus's predicate. -/
def Host.sinksAreTables (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ m : BusMessage p, bs.isStateful m.1 = false → hA.busEffect m ≠ 0 →
      ∀ mult : ZMod p, mult ≠ 0 → bs.accepts ⟨m.1, mult, m.2⟩

/-- Whether anything in the run actively touches `m`: a guest instance carries it with a nonzero
    multiplicity, or a host-chip instance nets something there.

    The invariant argument below runs over exactly these messages. A message *nobody* touches
    carries whatever payload the quantifier hands it, and nothing in a satisfying run forces that
    to be good — so it is not something the induction can be asked to prove. -/
def VmAssignment.activeAt {vm : Vm p} (a : VmAssignment p vm) (m : BusMessage p) : Prop :=
  (∃ (t : Fin vm.guest.length) (asg : ChipAssignment p), asg ∈ a.guestAssignments t ∧
      ∃ bi ∈ (vm.guest.get t).busInteractions,
        ((bi.eval asg).busId, (bi.eval asg).payload) = m ∧ (bi.eval asg).multiplicity ≠ 0)
  ∨ (∃ (t : Fin vm.host.chips.length) (c : BusState p), c ∈ a.hostAssignment t ∧ c m ≠ 0)

/-- **What the host does at a stateful message whose payload might be bad.** Either the payload
    is good after all, or the host's whole net there is *minus an honest count* `k` — a pile of
    receives that, with the guests' own, is too small to wrap `ZMod p`.

    Stated over a whole satisfying run, and with the lower ranks already settled, because that is
    what a real VM can actually deliver. Neither clause may be strengthened to "every message a
    host chip touches is good": a host chip that *reads* memory does not constrain the value it
    finds there any more than a guest does — OpenVM's `Rv32HintStoreAir` range-checks the hint it
    writes and neither the word it overwrites nor the pointer register it peeks. What it does
    instead is *echo*: the record it re-sends is one it received at a strictly smaller rank, which
    is exactly what the induction hypothesis vouches for. So a host chip is held to the same
    standard as a guest's `StepLayout.memSendsOk`, no more.

    The `k = 0` clause is what makes the pile a genuine pigeonhole for a message only the host
    touches: a vanishing count means the host chips did not touch it at all. -/
def Host.statefulChipsMaintain (host : Host p) (bs : BusSemantics p) (rm : RankModel p)
    (r0 : GuestBusRules p)
    (hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩) : Prop :=
  ∀ (G : Guest p), host.legalGuests G →
    ∀ a : VmAssignment p ⟨host, G⟩, VmSat ⟨host, G⟩ a →
      ∀ m : BusMessage p, bs.isStateful m.1 = true →
        (∀ m' : BusMessage p, bs.isStateful m'.1 = true → rm.rank m' < rm.rank m →
          a.activeAt m' → (bs.toGuestRules r0 hmem).payloadOk m') →
        (bs.toGuestRules r0 hmem).payloadOk m ∨
          ∃ k : ℕ, host.maxInteractions * host.maxInstances + k < p ∧
            a.hostAssignment.busEffect m = -((k : ℕ) : ZMod p) ∧
            (k = 0 → ∀ t : Fin host.chips.length, ∀ c ∈ a.hostAssignment t, c m = 0)

/-- The host can re-balance a stateless change: given a legal host assignment and a `δ` supported
    on stateless messages the semantics accepts, some legal host assignment nets exactly `δ` more,
    **leaving every IO-labeled chip alone**.

    Lookup host chips are free in exactly this way: their legality predicate constrains *which*
    payloads may carry a nonzero net multiplicity, not what that multiplicity is, so the change is
    absorbed into what they already net rather than by adding instances. The `isIo` clause is what
    makes the observed effect survive the rebuild.

    Note what this does *not* permit: every IO-labeled chip is pinned, so the observed `VmEffect`
    is carried across untouched. -/
def Host.absorbsStateless (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ hA : HostAssignment p host, hA.satisfies →
    ∀ δ : BusState p,
      (∀ m : BusMessage p, δ m ≠ 0 →
        bs.isStateful m.1 = false ∧
          ∃ mult : ZMod p, mult ≠ 0 ∧ bs.accepts ⟨m.1, mult, m.2⟩) →
      ∃ hA' : HostAssignment p host, hA'.satisfies ∧ hA'.busEffect = hA.busEffect + δ ∧
        ∀ i : Fin host.chips.length, (host.chips.get i).isIo = true → hA' i = hA i

/-- **The host turns a step's offsets into a rank order.** A claim about the VM, not about any
    guest circuit: whatever *legal* chips it is running, in a satisfying assignment within the
    trace budget, two interactions of one instance placed in the same step compare by rank the way
    they compare by offset.

    The hypotheses are exactly `Host.forcesAccepts`'s, and they are not decoration — without them
    the statement is false. A chip whose only traffic is a self-cancelling memory send/receive pair
    at some huge timestamp balances, satisfies `VmSat`, and violates the conclusion; legality is
    what excludes it, and the trace budget is what stops a run from wrapping `ZMod p` by sheer
    length.

    For OpenVM this is proved: `openVmHost_ordersRanks`, by walking the execution bridge
    (`Chain.lean`). Each step advances the bridge by a bounded positive amount
    (`StepLayout`), so a cycle among the steps would have to sum to zero over a total the budget
    keeps strictly between `0` and `p`; the connector — carrying OpenVM's range check as
    `ConnectorBoundary.finalTimestampBounded` — is therefore the only place a chain can start, and
    one checked timestamp places every step in the run. -/
def Host.ordersRanks (host : Host p) (rm : RankModel p) (r : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p))) : Prop :=
  ∀ (G : Guest p),
    host.legalGuests G →
    ∀ (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a →
      a.ordersRanks rm r memAddress host.maxWindow host.maxLookback

/-- **A host realizes its bus semantics.** The single hypothesis the connecting theorems need of
    the fixed VM; see the module docstring. (The lemmas below still take the individual fields, so
    which one carries which step stays visible.)

    `r0` is the clock template `bs.toGuestRules` borrows its `execBusId`/`memBusId`/`getTimestamp`
    from — in practice `openVmGuestRules`'s own value; see `Legal.lean` for why it does not live
    on `rm`. -/
structure Host.realizes (host : Host p) (bs : BusSemantics p) (rm : RankModel p)
    (r0 : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p))) : Prop where
  /-- Off the memory bus, `bs` always has *some* multiplicity maintaining its invariants — what
      `bs.toGuestRules`'s `memPayloadOnly` field rests on (`Legal.lean`). -/
  hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
    ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩
  /-- The host's `Host.legalGuest` field is at least `Circuit.legalGuest` for `bs`, at this
      argument's own `rm.rank` and `rm.bound` and the host's own sizes. -/
  legalGuest : ∀ c : Circuit p,
    host.legalGuest c →
      c.legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback host.maxInteractions
  sinksAreTables : host.sinksAreTables bs
  /-- The one field that is not about a single chip: what the host's chips leave, together, at a
      message whose payload might be bad. -/
  statefulChipsMaintain : host.statefulChipsMaintain bs rm r0 hmem
  statefulAcceptsOfPayloadOk : bs.statefulAcceptsOfPayloadOk r0 hmem
  absorbsStateless : host.absorbsStateless bs
  ordersRanks : host.ordersRanks rm (bs.toGuestRules r0 hmem) memAddress

/-- The host chips realize `bs`'s acceptance: in any satisfying VM built on this host whose guest
    chips are small enough not to wrap `ZMod p`, every guest instance's assignment is
    `Circuit.satisfies`-good, not merely algebraically consistent.

    Every chip in `G` must be one the host will run: the balancing argument is over the whole
    list, so one illegal chip anywhere on a bus breaks it. That legality is also where the
    anti-wraparound bookkeeping comes from — `Circuit.legalGuest`'s `size` clause bounds each
    chip's bus-interaction count, and `Host.statefulChipsMaintain` budgets the host's own pile
    alongside it (see `Counting.lean`).

    Proved from `Host.realizes` — see `forcesAccepts_of_hostSound`. -/
def Host.forcesAccepts (host : Host p) (bs : BusSemantics p) : Prop :=
  ∀ (G : Guest p),
    host.legalGuests G →
    ∀ (a : VmAssignment p ⟨host, G⟩), VmSat ⟨host, G⟩ a →
      ∀ (t : Fin G.length), ∀ asg ∈ a.guestAssignments t, (G.get t).satisfies bs asg


/-- **A guest instance's lookups all hold**, in any satisfying run. This is the manuscript's
    `bus_int.tex` induction on the stateless buses: the host chips *are* the lookup tables, so an
    actively-sent stateless message has nowhere to go but into a chip that only receives table
    entries.

    Nothing stateful takes part — only `Circuit.statelessSendOnly`, `Host.sinksAreTables`, bus
    balance and the trace budget — which is what makes it safe to hand to `StepLayout.sendsOk`,
    whose own derivation depends on it. -/
theorem satisfiesStateless_of_sinks [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {r0 : GuestBusRules p}
    {hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩}
    {memAddress : BusMessage p → List (Option (ZMod p))}
    {G : Guest p} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c →
        c.legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback
          host.maxInteractions)
    (hsinks : host.sinksAreTables bs) (hGuests : host.legalGuests G)
    (hsat : VmSat ⟨host, G⟩ a)
    (t : Fin G.length) (asg : ChipAssignment p) (hasg : asg ∈ a.guestAssignments t) :
    (G.get t).satisfiesStateless (bs.toGuestRules r0 hmem) asg := by
  have hlegal : ∀ s : Fin G.length,
      (G.get s).legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback
        host.maxInteractions :=
    fun s => hunpack _ (hGuests _ (List.get_mem G s))
  have hSize : ∀ c ∈ G, c.busInteractions.length ≤ host.maxInteractions :=
    fun c hc => (hunpack c (hGuests c hc)).size
  have hBudget : host.maxInteractions * host.maxInstances < p := by
    have := host.noMultOverflow; omega
  intro bi hbi hst hmult
  have hm : bs.isStateful ((bi.eval asg).busId, (bi.eval asg).payload).1 = false := hst
  have huni : ∀ s : Fin G.length, ∀ asg' ∈ a.guestAssignments s,
      (G.get s).uniformAt asg' ((bi.eval asg).busId, (bi.eval asg).payload) 1 := by
    intro s asg' hasg' bi' hbi' hmsg'
    refine (hlegal s).sendOnly asg' (hsat.satisfiesGuest s asg' hasg') bi' hbi' ?_
    rw [show bi'.busId = (bi.eval asg).busId from congrArg Prod.fst hmsg']
    exact hst
  have hguest :=
    guestNet_ne_zero_of_uniform hsat hSize hBudget one_ne_zero huni hasg hbi rfl hmult
  have hbal := hsat.balances ((bi.eval asg).busId, (bi.eval asg).payload)
  have hhost : a.hostAssignment.busEffect ((bi.eval asg).busId, (bi.eval asg).payload) ≠ 0 := by
    intro h
    exact hguest (by rw [busEffect_apply, h, add_zero] at hbal; exact hbal)
  exact hsinks a.hostAssignment (hsat.satisfiesHost) _ hm hhost (bi.eval asg).multiplicity hmult

/-- **The stateful analogue of the manuscript's stateless induction — its `eq:legal:recv_byte`.**
    In a satisfying VM, every stateful message anything in the run actively touches carries a
    payload that maintains the bus invariants.

    For a guest's *send* that is the chip's own obligation (`StepLayout.memSendsOk`); for a host
    chip's, `Host.statefulChipsMaintain`'s. For a *receive* it is forced by balancing: if nothing
    carrying that payload maintained the invariants then no guest sent it and no host chip sent it
    either, leaving a pile of receives that cannot sum to zero — which is where the trace budget
    is needed again, since `p` receives would.

    The whole thing is a strong induction on `rm.rank`, and it has to be: balance alone
    cannot establish the invariant, because two chips can each receive a bad payload and send
    another one, cancelling perfectly. What kills that is the rank — one of the two chips would
    have to send below the rank it received at. A sender may therefore lean on everything touched
    at a strictly smaller rank, which is exactly the induction hypothesis; both the guest clause
    and the host one are stated to take it, and the host side needs it for the same reason a guest
    does (`Host.statefulChipsMaintain`). -/
theorem maintains_of_stateful_active [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p}
    {hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩}
    {memAddress : BusMessage p → List (Option (ZMod p))}
    {G : Guest p} {a : VmAssignment p ⟨host, G⟩}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c →
        c.legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback
          host.maxInteractions)
    (hsinks : host.sinksAreTables bs)
    (hstateful : host.statefulChipsMaintain bs rm r0 hmem)
    (hGuests : host.legalGuests G)
    (hsat : VmSat ⟨host, G⟩ a)
    (hOrders : a.ordersRanks rm (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback)
    {m : BusMessage p} (hst : bs.isStateful m.1 = true) (hact : a.activeAt m) :
    (bs.toGuestRules r0 hmem).payloadOk m := by
  have hSize : ∀ c ∈ G, c.busInteractions.length ≤ host.maxInteractions :=
    fun c hc => (hunpack c (hGuests c hc)).size
  have hlegal : ∀ s : Fin G.length,
      (G.get s).legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback
        host.maxInteractions :=
    fun s => hunpack _ (hGuests _ (List.get_mem G s))
  suffices key : ∀ r : ℕ, ∀ msg : BusMessage p, rm.rank msg = r → bs.isStateful msg.1 = true →
      a.activeAt msg → (bs.toGuestRules r0 hmem).payloadOk msg by
    exact key _ m rfl hst hact
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro msg hrank hstm hactm
  by_contra hno
  -- Everything of strictly smaller rank that anybody touches is already good.
  have hIH : ∀ m' : BusMessage p, bs.isStateful m'.1 = true → rm.rank m' < rm.rank msg →
      a.activeAt m' → (bs.toGuestRules r0 hmem).payloadOk m' :=
    fun m' hst' hlt hact' => ih (rm.rank m') (hrank ▸ hlt) m' rfl hst' hact'
  -- The payload is not good, hence no guest *sends* it: every guest multiplicity is `0` or `-1`.
  have huni : ∀ u : Fin G.length, ∀ asg'' ∈ a.guestAssignments u,
      (G.get u).uniformAt asg'' msg (-1) := by
    intro u asg'' hasg'' bi'' hbi'' hmsg''
    have hbus : bi''.busId = msg.1 := congrArg Prod.fst hmsg''
    have hstb : bs.isStateful bi''.busId = true := by rw [hbus]; exact hstm
    rcases (hlegal u).polarity asg'' (hsat.satisfiesGuest u asg'' hasg'') bi'' hbi'' hstb with
      h0 | h1 | hm1
    · exact Or.inl h0
    · -- A send has to vouch for itself, given everything it touched earlier that is *also on the
      -- memory bus* — which the induction hypothesis supplies, because a step's offsets order
      -- ranks. Off the memory bus, `memPayloadOnly` settles it outright: no induction needed.
      obtain ⟨i, hi⟩ := List.get_of_mem hbi''
      have hsti : (bs.toGuestRules r0 hmem).isStateful
          ((G.get u).busInteractions.get i).busId = true := by rw [hi]; exact hstb
      have hmulti : (((G.get u).busInteractions.get i).eval asg'').multiplicity = 1 := by
        rw [hi]; exact h1
      have hmsgi : (G.get u).msgAt asg'' i = msg := by
        rw [Circuit.msgAt, hi]; exact hmsg''
      have hsendi : (G.get u).statefulSend (bs.toGuestRules r0 hmem) asg'' i := ⟨hsti, hmulti⟩
      refine absurd ?_ hno
      rw [← hmsgi]
      by_cases hbmem :
          ((G.get u).busInteractions.get i).busId = (bs.toGuestRules r0 hmem).memBusId
      · have hacc : (G.get u).satisfiesStateless (bs.toGuestRules r0 hmem) asg'' :=
          satisfiesStateless_of_sinks hunpack hsinks hGuests hsat u asg'' hasg''
        obtain ⟨L⟩ := (hlegal u).stepLayout asg'' (hsat.satisfiesGuest u asg'' hasg'') hacc
        refine L.memSendsOk i ⟨hsendi, hbmem⟩ (fun j hoff hactMemj => ?_)
        have hlt := hOrders u asg'' hasg'' L i j ⟨hsti, by rw [hsendi.2]; exact one_ne_zero⟩
          hactMemj.1 hoff
        rw [hmsgi] at hlt
        exact hIH _ hactMemj.1.1 hlt
          (Or.inl ⟨u, asg'', hasg'', _, List.get_mem _ _, rfl, hactMemj.1.2⟩)
      · exact (bs.toGuestRules r0 hmem).memPayloadOnly _ hsti hbmem
    · exact Or.inr hm1
  -- Nor does the host: what it leaves at `msg` is minus an honest count of its own receives.
  obtain ⟨k, hbud, hhost, hzero⟩ := (hstateful G hGuests a hsat msg hstm hIH).resolve_left hno
  -- Somebody touched `msg`, so that pile is not empty — and a pile of receives cannot balance.
  have hne : a.guestAssignments.count msg ≠ 0 ∨ k ≠ 0 := by
    rcases hactm with ⟨u, asg'', hasg'', bi'', hbi'', hmsg'', hmult''⟩ | ⟨u, c, hc, hcm⟩
    · exact Or.inl (count_ne_zero_of_active hasg'' hbi'' hmsg'' hmult'')
    · exact Or.inr (fun hk => hcm (hzero hk u c hc))
  exact net_ne_zero_of_recvs hsat hSize hbud huni hhost hne (hsat.balances msg)

/-- **`Host.forcesAccepts` is derivable.** Honest table sinks on the stateless buses, host chips
    that maintain the invariants on the stateful ones, bus semantics whose stateful acceptance
    follows from those invariants, and the anti-wraparound budget together give every guest
    instance the full `Circuit.satisfies` — not just its algebraic constraints, and with no
    assumption about acceptance placed on the guest chips themselves. -/
theorem forcesAccepts_of_hostSound [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p}
    {hmem : ∀ m : BusMessage p, bs.isStateful m.1 = true → m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, bs.maintainsInvariants ⟨m.1, mult, m.2⟩}
    {memAddress : BusMessage p → List (Option (ZMod p))}
    (hunpack : ∀ c : Circuit p,
      host.legalGuest c →
        c.legalGuest (bs.toGuestRules r0 hmem) memAddress host.maxWindow host.maxLookback
          host.maxInteractions)
    (hsinks : host.sinksAreTables bs)
    (hstateful : host.statefulChipsMaintain bs rm r0 hmem)
    (hbs : bs.statefulAcceptsOfPayloadOk r0 hmem)
    (hord : host.ordersRanks rm (bs.toGuestRules r0 hmem) memAddress) :
    host.forcesAccepts bs := by
  intro G hGuests a hsat t asg hasg
  have hRanks := hord G hGuests a hsat
  refine ⟨hsat.satisfiesGuest t asg hasg, fun bi hbi hmult => ?_⟩
  by_cases hst : bs.isStateful bi.busId
  · exact hbs _ hst (maintains_of_stateful_active hunpack hsinks hstateful hGuests
      hsat hRanks hst (Or.inl ⟨t, asg, hasg, bi, hbi, rfl, hmult⟩))
  · exact satisfiesStateless_of_sinks hunpack hsinks hGuests hsat t asg hasg bi hbi
      (by simpa using hst) hmult

/-- `Host.realizes` gives `Host.forcesAccepts`. -/
theorem Host.realizes.forcesAccepts [Fact p.Prime] {host : Host p} {bs : BusSemantics p}
    {rm : RankModel p} {r0 : GuestBusRules p}
    {memAddress : BusMessage p → List (Option (ZMod p))}
    (h : host.realizes bs rm r0 memAddress) :
    host.forcesAccepts bs :=
  forcesAccepts_of_hostSound h.legalGuest h.sinksAreTables h.statefulChipsMaintain
    h.statefulAcceptsOfPayloadOk h.ordersRanks
