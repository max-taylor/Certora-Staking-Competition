import "./erc20.spec"

using DummyERC20A as stakingToken
using DummyERC20B as rewardsToken
/**************************************************
 *              METHODS DECLARATIONS              *
 **************************************************/
methods{
    stakingToken()                  returns (address)   envfree
    rewardsToken()                  returns (address)   envfree
    owner()                         returns (address)   envfree
    duration()                      returns (uint256)   envfree
    finishAt()                      returns (uint256)   envfree
    updatedAt()                     returns (uint256)   envfree
    rewardRate()                    returns (uint256)   envfree
    rewardPerTokenStored()          returns (uint256)   envfree
    userRewardPerTokenPaid(address) returns (uint256)   envfree
    rewards(address)                returns (uint256)   envfree
    totalSupply()                   returns (uint256)   envfree
    balanceOf(address)              returns (uint256)   envfree
    _min(uint256, uint256)          returns(uint256)    envfree
    rewardsToken.balanceOf(address) returns (uint256)   envfree
    stakingToken.balanceOf(address) returns (uint256)   envfree
    lastTimeRewardApplicable()      returns (uint256)
    rewardPerToken()                returns (uint256)
    earned(address)                 returns uint256 
    stake(uint256)
    withdraw(uint256)
    getReward(address)
    setRewardsDuration(uint256)
    notifyRewardAmount(uint256)
    getNotifyUpdatedRewardRate(uint256) returns uint256
}



//  *** Ghosts

ghost mathint ghostSumOfBalances {
	init_state axiom ghostSumOfBalances == 0 ;
}

hook Sstore balanceOf [KEY address account] uint256 newValue (uint256 oldValue) STORAGE {
  ghostSumOfBalances = ghostSumOfBalances + newValue - oldValue;
}

// This ensures that the account balances aren't initialized to be greater than the total supply, this will result in overflow
hook Sload uint256 val balanceOf[KEY address account] STORAGE {
    require ghostSumOfBalances >= val;
}

// **** Valid states

// @audit-ok
invariant totalSupplyIsSumOfBalances()
  totalSupply() == ghostSumOfBalances

// @audit-ok
invariant finishAtGreaterEqualThanBlocktimestamp(env e)
  // Finish at is initialized at 0, so skip this pre-condition
  finishAt() != 0 => finishAt() >= e.block.timestamp
  {
    preserved with (env e1) {
      // Ensures that a parametric method doesn't have a lower block.timestamp than the pre-hook
      require e1.block.timestamp >= e.block.timestamp;
    }
  }

// @audit-ok
// When updatedAt is updated, it calls lastTimeRewardApplicable to get the min of finishAt or block.timestamp. If finishAt is 0, then updatedAt should be set to 0.
invariant finishAtZeroThenUpdatedAtZero()
  finishAt() == 0 => updatedAt() == 0
  {
    preserved with (env e) {
      // Safe assumption
      require e.block.timestamp > 0;
    }
  }

// @audit-ok
// Ensures updatedAt never exceeds block.timestamp
invariant updatedAtLessEqualBlocktimestamp(env e)
  updatedAt() <= e.block.timestamp
  {
    preserved with (env e1) {
      // Ensures the parametric method uses the same block.timestamp
      require e1.block.timestamp == e.block.timestamp;
    }
  }

// @audit-ok
// updatedAt should never exceed lastTimeRewardApplicable
invariant lastTimeRewardApplicableGreaterEqualUpdatedAt(env e)
  lastTimeRewardApplicable(e) >= updatedAt()
  {
    preserved with (env e1) {
      require e1.block.timestamp == e.block.timestamp;
      requireInvariant updatedAtLessEqualBlocktimestamp(e1);
    }
  }

// *** Unit test

// @audit-ok
rule updatedAtShouldOnlyIncrease(method f, env e, calldataarg args) {
  requireInvariant finishAtGreaterEqualThanBlocktimestamp(e);
  requireInvariant updatedAtLessEqualBlocktimestamp(e);
  requireInvariant finishAtZeroThenUpdatedAtZero();

  mathint updatedAtBefore = updatedAt();

  f(e, args);

  mathint updatedAtAfter = updatedAt();

  assert updatedAtAfter >= updatedAtBefore, "Updated at should only ever increase if finishAt has been set";
}

// @audit-ok
rule userRewardsStopIncreasingAfterRewardExpiry(address user) {
  env e;
  // Ensure the reward duration has expired
  require e.block.timestamp >= finishAt();

  // Cache the reward value
  mathint earned1 = earned(e, user);

  env e1;

  require e1.block.timestamp >= e.block.timestamp;
  
  mathint earned2 = earned(e1, user);

  assert earned1 == earned2, 
    "User's earned rewards should stop increasing after reward duration expires";
}

// @audit-ok
rule rewardPerTokenStopsIncreasingAfterFinish() {
  env e;
  
  require e.block.timestamp >= finishAt();

  mathint rewardPerTokenBefore = rewardPerToken(e);

  env e1;
  require e1.block.timestamp >= e.block.timestamp;

  mathint rewardPerTokenAfter = rewardPerToken(e1);

  assert rewardPerTokenBefore == rewardPerTokenAfter;
}

// @audit-ok
rule onlySpecificConditionsCanModifyRewardDuration(method f, env e){
  uint256 _duration = duration();
  calldataarg args;
  f(e, args);
  uint256 duration_ = duration();

  assert _duration != duration_ => 
    (
      f.selector == setRewardsDuration(uint256).selector && 
      e.msg.sender == owner() &&
      finishAt() < e.block.timestamp
    );
}

// ** Notify reward amount

// If block.timestamp >= finishAt => rewardRate == _amount / duration
// Else block.timestamp < finishAt => rewardRate == amount + ((finishAt - block.timestamp) * rewardRate) / duration
// finishAt == block.timestamp + duration
// updatedAt == block.timestamp

// It should always revert if duration == 0

// @audit-ok
rule notifyRewardAmountShouldRevertIffConditions() {
  env e;
  requireInvariant finishAtZeroThenUpdatedAtZero();
  requireInvariant updatedAtLessEqualBlocktimestamp(e);

  uint256 amount;
  uint256 updatedRewardRate = getNotifyUpdatedRewardRate(e, amount);

  notifyRewardAmount@withrevert(e, amount);

  bool reverted = lastReverted;

  assert updatedRewardRate == 0 => reverted;
  assert updatedRewardRate * duration() > rewardsToken.balanceOf(currentContract) => reverted;
  
  // ! Note this assertion results in an overflow in rewardPerToken, block.timestamp is set extremely high, or rewardRate is
  // assert reverted <=> (
  //   updatedRewardRate == 0 ||
  //   updatedRewardRate * duration() > rewardsToken.balanceOf(currentContract) ||
  //   e.msg.sender != owner()
  // );
}

// @audit-ok
rule finishAtOnlyUpdatedByNotifyRewardAmount() {
  env e; method f; calldataarg args;

  uint256 finishAtBefore = finishAt();
  f(e, args);

  assert finishAt() != finishAtBefore => 
    f.selector == notifyRewardAmount(uint256).selector;
}

// rule updatedAtOnlyUpdatedBySelectMethods() {}

// It should always revert when calling admin methods from a non-admin account

// @audit-ok
rule shouldAlwaysRevertCallingOwnerMethodsFromNonOwner(method f, env e, calldataarg args) 
  filtered {
    f -> ownerOnlyMethods(f)
  } 
{
  require owner() != e.msg.sender;

  f@withrevert(e, args);

  assert lastReverted, "Should always revert when calling admin methods from non-admin account";
}

// **** High-level

// @audit-ok
rule userShouldAlwaysBeAbleToWithdrawStakedAmount(env e, uint256 amount) {
  stake(e, amount);

  withdraw@withrevert(e, amount);

  assert !lastReverted, "Withdrawing the staked assets should never revert";
}

// **** Risk-assessment

// @audit-ok
rule userShouldOnlyBeAbleToWithdrawTheirBalance(env e) {
  uint256 userBalance = balanceOf(e.msg.sender);

  withdraw(e, userBalance);

  uint256 amount;

  withdraw@withrevert(e, amount);

  assert lastReverted, "Withdrawing more than the user's balance should revert";
}

rule userShouldAlwaysBeAbleToClaimRewards(env e) {
  getReward@withrevert(e);

  assert !lastReverted, "User should always be able to claim their rewards";
}

// *** HELPERS

definition ownerOnlyMethods(method f) returns bool =
  f.selector == setRewardsDuration(uint256).selector ||
  f.selector == notifyRewardAmount(uint256).selector;

function globalRequires(env e) {
  require e.msg.sender != 0;
  require e.msg.sender != currentContract;
  require e.msg.sender != rewardsToken;
  require e.msg.sender != stakingToken;
  require rewardsToken != stakingToken;
  require stakingToken != currentContract;
  require rewardsToken != currentContract;

  requireInvariant totalSupplyIsSumOfBalances();
}