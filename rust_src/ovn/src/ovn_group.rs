// #[hax_lib::exclude]
// use hax_lib::*;

#[hax_lib_macros::exclude]
use hacspec_concordium::*;
#[hax_lib_macros::exclude]
use hacspec_concordium_derive::*;

pub use crate::ovn_traits::*;

////////////////////////
// Useful definitions //
////////////////////////

pub fn sub<Z: Field>(x: Z, y: Z) -> Z {
    Z::add(x, Z::opp(y))
}

pub fn div<G: Group>(x: G, y: G) -> G {
    G::prod(x, G::group_inv(y))
}

////////////////////
// Implementation //
////////////////////

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct SchnorrZKPCommit<G: Group> {
    pub schnorr_zkp_u: G,
    pub schnorr_zkp_c: G::Z,
    pub schnorr_zkp_z: G::Z,
}

/** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) */
// https://www.rfc-editor.org/rfc/rfc8235
// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp<G: Group>(random: G::Z, h: G, x: G::Z) -> SchnorrZKPCommit<G> {
    let r = random;
    let u = G::g_pow(r);
    let c = G::hash(vec![G::g(), h, u]);
    let z = G::Z::add(r, G::Z::mul(c, x));

    return SchnorrZKPCommit {
        schnorr_zkp_u: u,
        schnorr_zkp_c: c,
        schnorr_zkp_z: z,
    };
}

// https://crypto.stanford.edu/cs355/19sp/lec5.pdf
pub fn schnorr_zkp_validate<G: Group>(h: G, pi: SchnorrZKPCommit<G>) -> bool {
    pi.schnorr_zkp_c == G::hash(vec![G::g(), h, pi.schnorr_zkp_u])
        && G::g_pow(pi.schnorr_zkp_z) == G::prod(pi.schnorr_zkp_u, G::pow(h, pi.schnorr_zkp_c))
}

#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OrZKPCommit<G: Group> {
    pub or_zkp_x: G,
    pub or_zkp_y: G,
    pub or_zkp_a1: G,
    pub or_zkp_b1: G,
    pub or_zkp_a2: G,
    pub or_zkp_b2: G,

    pub or_zkp_c: G::Z,

    pub or_zkp_d1: G::Z,
    pub or_zkp_d2: G::Z,

    pub or_zkp_r1: G::Z,
    pub or_zkp_r2: G::Z,
}

/** Cramer, Damgård and Schoenmakers (CDS) technique */
pub fn zkp_one_out_of_two<G: Group>(
    random_w: G::Z,
    random_r: G::Z,
    random_d: G::Z,
    h: G,
    xi: G::Z,
    vi: bool,
) -> OrZKPCommit<G> {
    let w = random_w;

    if vi {
        let r1 = random_r;
        let d1 = random_d;

        let x = G::g_pow(xi);
        let y = G::prod(G::pow(h, xi), G::g());

        let a1 = G::prod(G::g_pow(r1), G::pow(x, d1));
        let b1 = G::prod(G::pow(h, r1), G::pow(y, d1));

        let a2 = G::g_pow(w);
        let b2 = G::pow(h, w);

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d2 = sub::<G::Z>(c, d1);
        let r2 = sub::<G::Z>(w, G::Z::mul(xi, d2));

        OrZKPCommit {
            or_zkp_x: x,
            or_zkp_y: y,
            or_zkp_a1: a1,
            or_zkp_b1: b1,
            or_zkp_a2: a2,
            or_zkp_b2: b2,
            or_zkp_c: c,
            or_zkp_d1: d1,
            or_zkp_d2: d2,
            or_zkp_r1: r1,
            or_zkp_r2: r2,
        }
    } else {
        let r2 = random_r;
        let d2 = random_d;

        let x = G::g_pow(xi);
        let y = G::pow(h, xi);

        let a1 = G::g_pow(w);
        let b1 = G::pow(h, w);

        let a2 = G::prod(G::g_pow(r2), G::pow(x, d2));
        let b2 = G::prod(G::pow(h, r2), G::pow(div::<G>(y, G::g()), d2));

        let c = G::hash(vec![x, y, a1, b1, a2, b2]);

        let d1 = sub::<G::Z>(c, d2);
        let r1 = sub::<G::Z>(w, G::Z::mul(xi, d1));

        OrZKPCommit {
            or_zkp_x: x,
            or_zkp_y: y,
            or_zkp_a1: a1,
            or_zkp_b1: b1,
            or_zkp_a2: a2,
            or_zkp_b2: b2,
            or_zkp_c: c,
            or_zkp_d1: d1,
            or_zkp_d2: d2,
            or_zkp_r1: r1,
            or_zkp_r2: r2,
        }
    }
}

// Anonymous voting by two-round public discussion
pub fn zkp_one_out_of_two_validate<G: Group>(h: G, zkp: OrZKPCommit<G>) -> bool {
    let c = G::hash(vec![
        zkp.or_zkp_x,
        zkp.or_zkp_y,
        zkp.or_zkp_a1,
        zkp.or_zkp_b1,
        zkp.or_zkp_a2,
        zkp.or_zkp_b2,
    ]); // TODO: add i

    c == G::Z::add(zkp.or_zkp_d1, zkp.or_zkp_d2)
        && zkp.or_zkp_a1 == G::prod(G::g_pow(zkp.or_zkp_r1), G::pow(zkp.or_zkp_x, zkp.or_zkp_d1))
        && zkp.or_zkp_b1
            == G::prod(
                G::pow(h, zkp.or_zkp_r1),
                G::pow(zkp.or_zkp_y, zkp.or_zkp_d1),
            )
        && zkp.or_zkp_a2 == G::prod(G::g_pow(zkp.or_zkp_r2), G::pow(zkp.or_zkp_x, zkp.or_zkp_d2))
        && zkp.or_zkp_b2
            == G::prod(
                G::pow(h, zkp.or_zkp_r2),
                G::pow(div::<G>(zkp.or_zkp_y, G::g()), zkp.or_zkp_d2),
            )
}

pub fn commit_to<G: Group>(g_pow_xi_yi_vi: G) -> G::Z {
    G::hash(vec![g_pow_xi_yi_vi])
}

pub fn check_commitment<G: Group>(g_pow_xi_yi_vi: G, commitment: G::Z) -> bool {
    G::hash(vec![g_pow_xi_yi_vi]) == commitment
}

#[hax_lib_macros::contract_state(contract = "OVN")]
#[cfg_attr(not(hax), contract_state(contract = "OVN"))]
#[derive(Serialize, SchemaType, Clone, Copy)]
pub struct OvnContractState<G: Group, const n: usize> {
    pub g_pow_xis: [Option<G>; n],
    pub zkp_xis: [Option<SchnorrZKPCommit<G>>; n],

    pub register_count: u32,

    pub commit_vis: [Option<G::Z>; n],
    pub commit_count: u32,

    pub g_pow_xi_yi_vis: [Option<G>; n],
    pub zkp_vis: [Option<OrZKPCommit<G>>; n],
    pub vote_count: u32,

    pub tally: Option<u32>,
}

#[hax_lib_macros::init(contract = "OVN")]
#[cfg_attr(not(hax), init(contract = "OVN"))]
pub fn init_ovn_contract<G: Group, const n: usize>(
    _: &impl HasInitContext,
) -> InitResult<OvnContractState<G, n>> {
    Ok(OvnContractState::<G, n> {
        g_pow_xis: [None; n],
        zkp_xis: [None; n],
        register_count: 0,

        commit_vis: [None; n],
        commit_count: 0,

        g_pow_xi_yi_vis: [None; n],
        zkp_vis: [None; n],
        vote_count: 0,

        tally: None,
    })
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParamPublic<G: Group> {
    // public input
    pub rp_i: u32,
    // from private input
    pub rp_g_pow_xi: G,
    pub rp_zkp_xi: SchnorrZKPCommit<G>,
}

#[derive(Serialize, SchemaType)]
pub struct RegisterParamPrivate<Z: Field> {
    pub rp_xi: Z,
    pub rp_zkp_random: Z,
}

pub fn register_vote_private<G: Group>(
    params: RegisterParamPrivate<G::Z>,
) -> (G, SchnorrZKPCommit<G>) {
    let g_pow_xi = G::g_pow(params.rp_xi);
    let zkp_xi = schnorr_zkp::<G>(params.rp_zkp_random, g_pow_xi, params.rp_xi);
    (g_pow_xi, zkp_xi)
}

/** Primary function in round 1 */
#[hax_lib_macros::receive(
    contract = "OVN",
    name = "register",
    parameter = "RegisterParamPublic",
    generate_instance = true
)]
#[cfg_attr(not(hax),receive(contract = "OVN", name = "register", parameter = "RegisterParamPublic"))]
pub fn register_vote<G: Group, const n: usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: RegisterParamPublic<G> = ctx.parameter_cursor().get()?;

    if state.g_pow_xis[params.rp_i as usize].is_some()
        || state.zkp_xis[params.rp_i as usize].is_some()
    {
        return Err(ParseError {});
    }

    let mut register_vote_state_ret = state.clone();
    register_vote_state_ret.g_pow_xis[params.rp_i as usize] = Some(params.rp_g_pow_xi);
    register_vote_state_ret.zkp_xis[params.rp_i as usize] = Some(params.rp_zkp_xi);

    register_vote_state_ret.register_count += 1;

    Ok((A::accept(), register_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CommitVoteParamPublic<Z: Field> {
    // public
    pub cvp_i: u32,
    // from private
    pub cvp_commit_vi: Z,
}

#[derive(Serialize, SchemaType)]
pub struct CommitVoteParamPrivate<Z: Field> {
    // public
    pub cvp_i_: u32,
    // private
    pub cvp_xi: Z,
    pub cvp_zkp_random_w: Z,
    pub cvp_zkp_random_r: Z,
    pub cvp_zkp_random_d: Z,
    pub cvp_vote: bool,
}

pub fn compute_g_pow_yi<G: Group, const n: usize>(i: usize, xis: [G; n]) -> G {
    let mut prod1 = G::group_one();
    for j in 0..i {
        prod1 = G::prod(prod1, xis[j]);
    }

    let mut prod2 = G::group_one();
    for j in (i + 1)..n {
        prod2 = G::prod(prod2, xis[j]);
    }

    // implicitly: Y_i = g^y_i
    let g_pow_yi = div::<G>(prod1, prod2);
    g_pow_yi
}

pub fn compute_group_element_for_vote<G: Group>(xi: G::Z, vote: bool, g_pow_yi: G) -> G {
    G::prod(
        G::pow(g_pow_yi, xi),
        G::g_pow(if vote {
            G::Z::field_one()
        } else {
            G::Z::field_zero()
        }),
    )
}

/** Commitment before round 2 */
pub fn commit_to_vote_private<G: Group, const n: usize>(
    params: CommitVoteParamPrivate<G::Z>,
    g_pow_xis: [G; n],
) -> G::Z {
    let g_pow_yi = compute_g_pow_yi::<G, n>(params.cvp_i_ as usize, g_pow_xis);
    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.cvp_xi, params.cvp_vote, g_pow_yi);
    let commit_vi = commit_to::<G>(g_pow_xi_yi_vi);
    commit_vi
}

#[hax_lib_macros::receive(
    contract = "OVN",
    name = "commit_to_vote",
    parameter = "CommitVoteParamPublic",
    generate_instance = false
)]
#[cfg_attr(
    not(hax),
    receive(
        contract = "OVN",
        name = "commit_to_vote",
        parameter = "CommitVoteParamPublic"
    )
)]
pub fn commit_to_vote<G: Group, const n: usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: CommitVoteParamPublic<G::Z> = ctx.parameter_cursor().get()?;

    if state.register_count != n as u32 {
        return Err(ParseError {});
    }

    if state.commit_vis[params.cvp_i as usize].is_some() {
        return Err(ParseError {});
    }

    let zkp_xis_i = state.zkp_xis[params.cvp_i as usize].unwrap();
    let g_pow_xis_i = state.g_pow_xis[params.cvp_i as usize].unwrap();
    if !schnorr_zkp_validate(g_pow_xis_i, zkp_xis_i) {
        return Err(ParseError {});
    }

    let mut commit_to_vote_state_ret = state.clone();
    commit_to_vote_state_ret.commit_vis[params.cvp_i as usize] = Some(params.cvp_commit_vi);
    commit_to_vote_state_ret.commit_count += 1;
    Ok((A::accept(), commit_to_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParamPublic<G: Group> {
    // public
    pub vp_i: u32,
    // from private
    pub vp_zkp_vi: OrZKPCommit<G>,
    pub vp_g_pow_xi_yi_vi: G,
}

#[derive(Serialize, SchemaType)]
pub struct CastVoteParamPrivate<Z: Field> {
    // public
    pub vp_i_: u32,
    // private
    pub vp_xi: Z,
    pub vp_zkp_random_w: Z,
    pub vp_zkp_random_r: Z,
    pub vp_zkp_random_d: Z,
    pub vp_vote: bool,
}

pub fn cast_vote_private<G: Group, const n: usize>(
    params: CastVoteParamPrivate<G::Z>,
    g_pow_xis: [G; n],
) -> (OrZKPCommit<G>, G) {
    let g_pow_yi = compute_g_pow_yi::<G, n>(params.vp_i_ as usize, g_pow_xis);

    let zkp_vi = zkp_one_out_of_two::<G>(
        params.vp_zkp_random_w,
        params.vp_zkp_random_r,
        params.vp_zkp_random_d,
        g_pow_yi,
        params.vp_xi,
        params.vp_vote,
    );

    let g_pow_xi_yi_vi =
        compute_group_element_for_vote::<G>(params.vp_xi, params.vp_vote, g_pow_yi);

    (zkp_vi, g_pow_xi_yi_vi)
}

/** Primary function in round 2, also opens commitment */
#[hax_lib_macros::receive(
    contract = "OVN",
    name = "cast_vote",
    parameter = "CastVoteParamPublic",
    generate_instance = true
)]
#[cfg_attr(
    not(hax),
    receive(
        contract = "OVN",
        name = "cast_vote",
        parameter = "CastVoteParamPublic"
    )
)]
pub fn cast_vote<G: Group, const n: usize, A: HasActions>(
    ctx: &impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    let params: CastVoteParamPublic<G> = ctx.parameter_cursor().get()?;

    if state.commit_count != n as u32 {
        return Err(ParseError {});
    }

    if state.g_pow_xi_yi_vis[params.vp_i as usize].is_some()
        || state.zkp_vis[params.vp_i as usize].is_some()
    {
        return Err(ParseError {});
    }

    if !check_commitment::<G>(
        params.vp_g_pow_xi_yi_vi,
        state.commit_vis[params.vp_i as usize].unwrap(),
    ) {
        return Err(ParseError {});
    }

    let g_pow_yi =
        compute_g_pow_yi::<G, n>(params.vp_i as usize, state.g_pow_xis.map(|x| x.unwrap()));
    if !zkp_one_out_of_two_validate::<G>(g_pow_yi, params.vp_zkp_vi) {
        return Err(ParseError {});
    }

    let mut cast_vote_state_ret = state.clone();
    cast_vote_state_ret.g_pow_xi_yi_vis[params.vp_i as usize] = Some(params.vp_g_pow_xi_yi_vi);
    cast_vote_state_ret.zkp_vis[params.vp_i as usize] = Some(params.vp_zkp_vi);
    cast_vote_state_ret.vote_count += 1;

    Ok((A::accept(), cast_vote_state_ret))
}

#[derive(Serialize, SchemaType)]
pub struct TallyParameter {}

#[hax_lib_macros::receive(
    contract = "OVN",
    name = "tally",
    parameter = "TallyParameter",
    generate_instance = true
)]
#[cfg_attr(
    not(hax),
    receive(contract = "OVN", name = "tally", parameter = "TallyParameter")
)]
/** Anyone can tally the votes */
pub fn tally_votes<G: Group, const n: usize, A: HasActions>(
    _: &impl HasReceiveContext,
    state: OvnContractState<G, n>,
) -> Result<(A, OvnContractState<G, n>), ParseError> {
    if state.vote_count != n as u32 {
        return Err(ParseError {});
    }

    let mut vote_result = G::group_one();
    for g_pow_vote in state.g_pow_xi_yi_vis.map(|x| x.unwrap()) {
        vote_result = G::prod(vote_result, g_pow_vote);
    }

    // TODO: more efficient "brute force":
    // - https://en.wikipedia.org/wiki/Baby-step_giant-step
    // - https://en.wikipedia.org/wiki/Discrete_logarithm#Algorithms
    let mut tally = 0;
    let mut curr = G::Z::field_zero();
    for i in 0..n as u32 {
        // Should be while, but is bounded by n anyways!
        if G::g_pow(curr) == vote_result {
            tally = i;
        }

        curr = G::Z::add(curr, G::Z::field_one());
    }

    let mut tally_votes_state_ret = state.clone();
    tally_votes_state_ret.tally = Some(tally);

    Ok((A::accept(), tally_votes_state_ret))
}

// https://github.com/stonecoldpat/anonymousvoting
