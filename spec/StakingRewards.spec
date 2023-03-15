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
    stakingToken.allowance(address, address) returns (uint256)   envfree
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

// TODO: remove
// https://github.com/OpenZeppelin/openzeppelin-contracts-upgradeable/blob/master/certora/specs/GovernorBase.spec

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

// ghost mathint stakingTokenBalanceSum {
// 	init_state axiom stakingTokenBalanceSum == 0 ;
// }

// hook Sload uint256 val stakingToken.balanceOf[KEY address account] STORAGE {
//   require stakingTokenBalanceSum <= val;
// }

// hook Sstore stakingToken.balanceOf [KEY address account] uint256 newValue (uint256 oldValue) STORAGE {
//   stakingTokenBalanceSum = stakingTokenBalanceSum + newValue - oldValue;
// }

////////////////////////////////////////////////////////////
//  ***************     Valid States     ***************  //
////////////////////////////////////////////////////////////


// @audit-ok
invariant totalSupplyIsSumOfBalances()
  totalSupply() == ghostSumOfBalances

// @audit-ok
// If finishAt is set, it must be set to greater than or equal to the block.timestamp
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

// @audit-ok
// This is only ever set to be equal to rewardPerTokenStored
invariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(address user)
  userRewardPerTokenPaid(user) <= rewardPerTokenStored()

invariant totalSupplyZeroRewardPerTokenEqualsStored(env e)
  totalSupply() == 0 => rewardPerToken(e) == rewardPerTokenStored()

// @audit-ok
invariant stakingContractSolvent()
  stakingToken.balanceOf(currentContract) >= totalSupply()
  {
    preserved with (env e) {
      require e.msg.sender != currentContract;
      requireInvariant totalSupplyIsSumOfBalances();
    }
  }

////////////////////////////////////////////////////////////
//  ***************     Unit tests       ***************  //
////////////////////////////////////////////////////////////

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
rule rewardPerTokenShouldStopIncreasingAfterFinish() {
  env e;
  
  require e.block.timestamp >= finishAt();

  mathint rewardPerTokenBefore = rewardPerToken(e);

  env e1;
  require e1.block.timestamp >= e.block.timestamp;

  mathint rewardPerTokenAfter = rewardPerToken(e1);

  assert rewardPerTokenBefore == rewardPerTokenAfter;
}

// @audit-ok
// It should always revert when calling admin methods from a non-admin account
rule shouldAlwaysRevertCallingOwnerMethodsFromNonOwner(method f, env e, calldataarg args) 
  filtered {
    f -> ownerOnlyMethods(f)
  } 
{
  require owner() != e.msg.sender;

  f@withrevert(e, args);

  assert lastReverted, "Should always revert when calling admin methods from non-admin account";
}

// @audit-ok
// lastTimeRewardApplicable should return finishAt() if the block.timestamp is greater than it, otherwise it should return finishAt()
rule lastTimeRewardApplicableResult(env e) {
  mathint result = lastTimeRewardApplicable(e);

  assert finishAt() < e.block.timestamp ?
    result == finishAt() :
    result == e.block.timestamp;
}

// @audit-ok
rule notifyRewardAmountShouldRevertIffConditions() {
  env e;
  // rule - shouldAlwaysRevertCallingOwnerMethodsFromNonOwner is checking the admin only methods
  require e.msg.sender == owner();
  requireInvariant finishAtGreaterEqualThanBlocktimestamp(e);
  requireInvariant finishAtZeroThenUpdatedAtZero();
  requireInvariant updatedAtLessEqualBlocktimestamp(e);

  require e.block.timestamp * duration() < max_uint256;

  uint256 amount;
  uint256 updatedRewardRate = getNotifyUpdatedRewardRate(e, amount);

  rewardPerToken(e);

  notifyRewardAmount@withrevert(e, amount);
  bool reverted = lastReverted;
  
  assert reverted <=> (
    updatedRewardRate == 0 ||
    updatedRewardRate * duration() > rewardsToken.balanceOf(currentContract)
  );
}

//  *** Staking

// @audit-ok
rule shouldRevertWhenTryingToStakeMoreThanBalance() {
  env e;
  uint256 amount;
  uint256 balance = stakingToken.balanceOf(e.msg.sender);

  require amount > balance;

  stake@withrevert(e, amount);

  assert lastReverted, "Should not be able to stake more than the user's balance";
}

// @audit-ok
// Requires a lot of pre-conditions, but works has a simple assertion for the conditions
rule stakeShouldRevertIffConditions() {
  env e; uint256 amount;
  globalRequires(e);

  require stakingToken.allowance(e.msg.sender, currentContract) >= amount;
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e.msg.sender);

  earned@withrevert(e, e.msg.sender);
  require !lastReverted;

  mathint balance = stakingToken.balanceOf(e.msg.sender);
  require balance + stakingToken.balanceOf(currentContract) < max_uint256;
  require totalSupply() + amount < max_uint256;

  stake@withrevert(e, amount);

  assert lastReverted <=> (
    amount > balance ||
    amount == 0
  ), "Should not be able to stake more than the user's balance";
}

// ** Withdraw

// @audit-ok
rule withdrawRevertIffConditions() {
  env e; uint256 amount;

  require stakingToken.balanceOf(currentContract) >= amount;
  require stakingToken.balanceOf(e.msg.sender) + amount <= max_uint256;
  require totalSupply() >= amount;

  earned@withrevert(e, e.msg.sender);
  require !lastReverted;

  mathint userBalance = balanceOf(e.msg.sender);

  withdraw@withrevert(e, amount);

  assert lastReverted <=> (
    userBalance < amount ||
    amount == 0
  ), "Withdrawing more than the user's balance should revert";
}

// rule updatedAtOnlyUpdatedBySelectMethods() {}

////////////////////////////////////////////////////////////
//  ***************   State Transitions  ***************  //
////////////////////////////////////////////////////////////

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
rule notifyRewardAmountShouldUpdateValues() {
  env e;
  uint256 amount;

  uint256 updatedRewardRate = getNotifyUpdatedRewardRate(e, amount);
  notifyRewardAmount(e, amount);

  assert finishAt() == e.block.timestamp + duration();
  assert updatedAt() == e.block.timestamp;
  assert rewardRate() == updatedRewardRate;
}

// @audit-ok
// Only the msg.sender can modify their reward values and they can only be modified by select methods
rule usersRewardValuesUpdatedOnSpecificFunctions(address account) {
  env e; method f; calldataarg args;
  mathint rewardsBefore = rewards(account);
  mathint userRewardPerTokenPaidBefore = userRewardPerTokenPaid(account);

  f(e, args);

  assert (
    rewards(account) != rewardsBefore || 
    userRewardPerTokenPaid(account) != userRewardPerTokenPaidBefore
  ) => (
    e.msg.sender == account &&
    userRewardUpdatingMethods(f)
  );
}

// @audit-ok
rule rewardPerTokenShouldOnlyIncrease() {
  env e; method f; calldataarg args;

  mathint rewardPerTokenBefore = rewardPerToken(e);
  f(e, args);

  assert rewardPerToken(e) >= rewardPerTokenBefore, "Reward per token stored can only increase";
}

// @audit-ok
rule userRewardPerTokenPaidShouldOnlyIncrease() {
  env e; method f; calldataarg args; address account;

  mathint userRewardPerTokenPaidBefore = userRewardPerTokenPaid(account);

  f(e, args);

  assert userRewardPerTokenPaid(account) >= userRewardPerTokenPaidBefore, "User reward per token paid should only increase";
}

// @audit-ok
rule antiMonotonicStakingBalances() {
  env e; method f; calldataarg args;
  globalRequires(e);

  mathint userBalanceBefore = stakingToken.balanceOf(e.msg.sender);
  mathint contractBalanceBefore = stakingToken.balanceOf(currentContract);
  f(e, args);

  mathint userBalanceAfter = stakingToken.balanceOf(e.msg.sender);
  mathint contractBalanceAfter = stakingToken.balanceOf(currentContract);

  assert (
    userBalanceBefore < userBalanceAfter => contractBalanceBefore > contractBalanceAfter
  ) && (
    userBalanceBefore > userBalanceAfter => contractBalanceBefore < contractBalanceAfter
  ), "Staking balances need to move together";
}

// @audit-ok
rule claimingRewardsShouldResetState() {
  env e; method f; calldataarg args;
  globalRequires(e);

  mathint tokenBalanceBefore = rewardsToken.balanceOf(e.msg.sender);
  mathint expectedRewards = earned(e, e.msg.sender);

  getReward(e);

  assert rewards(e.msg.sender) == 0;
  assert rewardsToken.balanceOf(e.msg.sender) - tokenBalanceBefore == expectedRewards;
}

// @audit-ok
rule rewardPerTokenUpdatedAtUpdatedBySelectMethods() {
  env e; method f; calldataarg args;

  mathint rewardPerTokenStoredBefore = rewardPerTokenStored();
  mathint updatedAtBefore = updatedAt();

  f(e, args);

  assert (
    rewardPerTokenStoredBefore != rewardPerTokenStored() || 
    updatedAtBefore != updatedAt()
  ) => updatedRewardMethods(f);
}


rule monotonicityForRewardEarningAndDuration() {
  env e1; env e2;
  require e2.block.timestamp > e1.block.timestamp;
  storage cacheStorage = lastStorage;

  address user; uint256 rewardAmount; uint256 depositAmount;

  mathint initialDuration = duration();

  // update the reward amount, using the duration in the contract
  notifyRewardAmount(e1, rewardAmount);
  
  // Determine the amount of rewards earned over the period
  mathint rewardsEnv1Before = earned(e1, user);
  withdraw(e2, depositAmount);
  mathint rewardsEnv2Before = earned(e2, user);

  mathint beforeSetRewardDiff = rewardsEnv2Before - rewardsEnv1Before;

  require beforeSetRewardDiff > 0;

  // Using the initial storage, update the duration
  uint256 newDuration;
  setRewardsDuration(e1, newDuration) at cacheStorage;
  cacheStorage = lastStorage;
  notifyRewardAmount(e1, rewardAmount) at cacheStorage;
  cacheStorage = lastStorage;

  // Determine rewards earned over the period
  mathint rewardsEnv1After = earned(e1, user) at cacheStorage;
  withdraw(e2, depositAmount);
  mathint rewardsEnv2After = earned(e2, user) at cacheStorage;

  mathint afterSetRewardDiff = rewardsEnv2After - rewardsEnv1After;

  assert (
    initialDuration > newDuration <=> 
    beforeSetRewardDiff < afterSetRewardDiff
  ) && (
    initialDuration < newDuration <=>
    beforeSetRewardDiff > afterSetRewardDiff
  );
}

////////////////////////////////////////////////////////////
//  *************** Variable Transitions ***************  //
////////////////////////////////////////////////////////////

// @audit-ok
rule finishAtOnlyUpdatedByNotifyRewardAmount() {
  env e; method f; calldataarg args;

  uint256 finishAtBefore = finishAt();
  f(e, args);

  assert finishAt() != finishAtBefore => 
    f.selector == notifyRewardAmount(uint256).selector;
}

// @audit-ok
rule notifyRewardAmountExpectedNewRewardRate() {
  env e;
  uint256 amount;
  mathint durationCache = duration();
  mathint rewardRateCache = rewardRate();
  mathint finishAtCache = finishAt();

  notifyRewardAmount(e, amount);

  mathint updatedRewardRate = rewardRate();

  // Matches the solidity logic, not ideal but is nice to check
  mathint remainingRewards = (finishAtCache - e.block.timestamp) * rewardRateCache;
  mathint expectedRewardRate = (amount + remainingRewards) / durationCache;

  assert e.block.timestamp >= finishAtCache ?
    updatedRewardRate == amount / durationCache :
    updatedRewardRate == expectedRewardRate;
}

// @audit-ok
rule onlySpecificConditionsCanModifyRewardDuration(method f, env e) {
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

////////////////////////////////////////////////////////////
// *************** High-level properties ***************  //
////////////////////////////////////////////////////////////

// Ensures that only the provided amount is taken from the user and that they can always withdraw it to get back their initial token balance
// @audit-ok
rule userCanAlwaysWithdrawAndGetSameAmountBack(env e, uint256 amount) {
  globalRequires(e);

  mathint initialTokenBalance = stakingToken.balanceOf(e.msg.sender);
  stake(e, amount);
  mathint afterStakingBalance = stakingToken.balanceOf(e.msg.sender);

  assert initialTokenBalance - afterStakingBalance == amount, "Only the amount should be taken from the user";

  withdraw@withrevert(e, amount);

  bool withdrawReverted = lastReverted;

  mathint finalUserTokenBalance = stakingToken.balanceOf(e.msg.sender);

  assert !withdrawReverted, "Withdrawing the staked assets should never revert";
  assert finalUserTokenBalance == initialTokenBalance, "User should have their initial token balance back";
}

// ! Seems very hard to prove
rule userActionShouldntAffectAbilityToWithdrawTokens() {
  env e1; env e2; method f; calldataarg args; uint256 amount;

  requireInvariant stakingContractSolvent();
  require balanceOf(e2.msg.sender) >= amount;
  require amount > 0;
  require e2.msg.value == 0;

  f(e1, args);

  withdraw@withrevert(e2, amount);

  assert !lastReverted, "User action shouldn't be able to affect ability to withdraw tokens";
}

rule userClaimingRewardsShouldntEffectOtherUsers() {
  env e1; env e2;
  requireInvariant stakingContractSolvent(); 
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e1.msg.sender);
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e2.msg.sender);

  globalRequires(e1);
  globalRequires(e2);

  require e2.block.timestamp >= e1.block.timestamp;
  require e2.msg.value == 0;

  mathint userBalanceBefore = rewardsToken.balanceOf(e2.msg.sender);

  mathint expectedReward = rewards(e2.msg.sender);

  require rewardsToken.balanceOf(currentContract) >= rewards(e1.msg.sender) + expectedReward;
  require userBalanceBefore + expectedReward <= max_uint256;
  

  earned(e2, e2.msg.sender); // Ensure a call to this can succeed

  getReward(e1);
  
  getReward@withrevert(e2);

  assert !lastReverted, "Users shouldn't affect other users claim to their rewards";
}

rule userShouldAlwaysBeAbleToClaimRewards() {
  env e1; env e2;
  // require e1 == e2;
  // require e1.block.timestamp != e2.block.timestamp;
  require e2.msg.value == 0;
  require e1.msg.sender == e2.msg.sender;
  require e2.block.timestamp >= e1.block.timestamp;

  earned(e1, e1.msg.sender);

  getReward@withrevert(e2);

  assert !lastReverted, "User should always be able to claim their share of rewards";
}


// ////////////////////////////////////////////////////////////
// // ***************    Risk assessment    ***************  //
// ////////////////////////////////////////////////////////////


// // @audit-ok
// rule ownerShouldNeverChange() {
//   env e; method f; calldataarg args;
//   address ownerBefore = owner();
//   f(e, args);

//   assert owner() == ownerBefore, "The owner should never change";
// }


// ////////////////////////////////////////////////////////////
// // ***************          Bugs         ***************  //
// ////////////////////////////////////////////////////////////

// // rule userStakesBeforeRoundStarts() {}

// // If a user stakes into a round and doesn't claim rewards before a new round is setup, they will receive no rewards for the previous round
// // ! If the rewardRate is updated through notifyRewardAmount, that will cause an immediate change in the amount of earned rewards
// rule bugUserDoesntClaimUntilNextRound() {
//   env e1; env e2;

//   // require e1.msg.sender == e2.msg.sender;
//   require e2.block.timestamp == e1.block.timestamp;
//   require rewardPerToken(e1) > 0;

//   uint256 amount;
//   stake(e1, amount);

//   uint256 earnedRewardsBefore = earned(e1, e1.msg.sender);
//   uint256 rewardAmount;
//   notifyRewardAmount(e2, rewardAmount);
//   uint256 earnedRewardsAfter = earned(e1, e1.msg.sender);

//   assert earnedRewardsAfter >= earnedRewardsBefore, "User shouldn't have reduced rewards after the reward amount is updated";
// }

// // If a user stakes before the round start, when the contract is in it's initial state, when the round starts and they claim rewards, they should receive the same rewards as someone who staked at round start
// rule bugUserStakesBeforeRoundStartShouldGetSameRewards() {
//   env e1; env e2;
//   // requireInvariant lastTimeRewardApplicableGreaterEqualUpdatedAt(e);

//   require e1.block.timestamp >= finishAt();
//   require e1.block.timestamp == e2.block.timestamp;

//   // Initial reward rate states are 0
//   // require rewardRate() == 0;
//   // require rewardPerTokenStored() == 0;
//   // Need to ensure that a user 
//   require rewardPerToken(e1) == 0;
//   require balanceOf(e1.msg.sender) == balanceOf(e2.msg.sender);
//   require rewards(e1.msg.sender) == rewards(e2.msg.sender);
//   require userRewardPerTokenPaid(e1.msg.sender) == 0;
//   require userRewardPerTokenPaid(e2.msg.sender) == 0;

//   uint256 amount;
//   stake(e1, amount);
//   // This should be the initial reward per token paid for the user
//   assert userRewardPerTokenPaid(e1.msg.sender) == 0;

//   uint256 rewardAmount;
//   notifyRewardAmount(e2, rewardAmount);
//   stake(e2, amount);

//   // env e1_1; env e2_2;
//   // require e1_1.msg.sender == e1.msg.sender && e1_1.block.timestamp > e1.block.timestamp;
//   // require e2_2.msg.sender == e2.msg.sender && e2_2.block.timestamp == e1_1.block.timestamp;

//   mathint rewardsEarned1 = getRewardsAndRewardsEarned(e1);
//   mathint rewardsEarned2 = getRewardsAndRewardsEarned(e2);

//   assert rewardsEarned1 == rewardsEarned2, "User has no rewards to claim";
// }

////////////////////////////////////////////////////////////
// ***************        Helpers        ***************  //
////////////////////////////////////////////////////////////

definition ownerOnlyMethods(method f) returns bool =
  f.selector == setRewardsDuration(uint256).selector ||
  f.selector == notifyRewardAmount(uint256).selector;

definition userRewardUpdatingMethods(method f) returns bool =
  f.selector == getReward().selector ||
  f.selector == withdraw(uint256).selector ||
  f.selector == stake(uint256).selector;

definition updatedRewardMethods(method f) returns bool =
  userRewardUpdatingMethods(f) ||
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

function getRewardsAndRewardsEarned(env e) returns mathint {
  mathint balanceBefore = rewardsToken.balanceOf(e.msg.sender);
  getReward(e);
  mathint balanceAfter = rewardsToken.balanceOf(e.msg.sender);

  return balanceAfter - balanceBefore;
}