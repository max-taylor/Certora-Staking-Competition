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
// Requires a lot of pre-conditions, but works has a simple assertion for the conditions
rule stakeShouldRevertIffConditions() {
  env e; uint256 amount;
  globalRequires(e);

  require stakingToken.allowance(e.msg.sender, currentContract) >= amount;
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e.msg.sender);

  // TODO: remove 
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

// @audit-ok
// A bit redundant but extra security
rule shouldRevertWhenTryingToStakeMoreThanBalance() {
  env e;
  uint256 amount;
  uint256 balance = stakingToken.balanceOf(e.msg.sender);

  require amount > balance;

  stake@withrevert(e, amount);

  assert lastReverted, "Should not be able to stake more than the user's balance";
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
// Only the msg.sender can modify their reward values and they can only be modified by select methods.
rule usersRewardValuesUpdatedOnSpecificFunctions(method f, address account) 
  filtered {
    // Ignore this method as it breaks the e.msg.sender == account assertion
    f -> f.selector != updateRewardHelper(address).selector
} {
  env e; calldataarg args;
  mathint rewardsBefore = rewards(account);
  mathint userRewardPerTokenPaidBefore = userRewardPerTokenPaid(account);

  mathint expectedNewRewards = f.selector != getReward().selector ? 
    earned(e, account) :
    0;

  mathint expectedUserRewardPerTokenPaid = rewardPerToken(e);

  f(e, args);

  mathint newRewards = rewards(account);
  mathint newUserRewardPerTokenPaid = userRewardPerTokenPaid(account);

  assert (
    newRewards != rewardsBefore || 
    newUserRewardPerTokenPaid != userRewardPerTokenPaidBefore
  ) => (
    e.msg.sender == account &&
    userRewardUpdatingMethods(f)
  );

  assert newRewards != rewardsBefore => 
    newRewards == expectedNewRewards, 
    "User's new reward value not equal to expected value";

  assert newUserRewardPerTokenPaid != userRewardPerTokenPaidBefore => 
    newUserRewardPerTokenPaid == expectedUserRewardPerTokenPaid, 
    "User's new reward per token paid not equal to expected value";
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

  mathint expectedRewardPerToken = rewardPerToken(e);

  // If calling notifyRewardAmount updatedAt will be the block.timestamp, otherwise the return valuue from lastTimeRewardApplicable
  mathint expectedUpdatedAt = f.selector != notifyRewardAmount(uint256).selector ? lastTimeRewardApplicable(e) : e.block.timestamp;

  f(e, args);

  mathint rewardPerTokenAfter = rewardPerTokenStored();
  mathint updatedAtAfter = updatedAt();

  assert (
    rewardPerTokenStoredBefore != rewardPerTokenAfter || 
    updatedAtBefore != updatedAtAfter
  ) => updatedRewardMethods(f);

  assert rewardPerTokenStoredBefore != rewardPerTokenAfter => 
    rewardPerTokenAfter == expectedRewardPerToken, 
    "Reward per token not updated to expected value";

  assert updatedAtBefore != updatedAtAfter => 
    updatedAtAfter == expectedUpdatedAt,
    "Updated at not set to expected value";
}

// ! Broken
rule monotonicityForRewardEarningAndDuration() {
  env e1; env e2;

  address user; uint256 rewardAmount; uint256 depositAmount;
  require user == e1.msg.sender;
  require e2.msg.sender == e1.msg.sender;
  require e2.block.timestamp > e1.block.timestamp;

  storage cacheStorage = lastStorage;

  mathint initialDuration = duration();

  // update the reward amount, using the duration in the contract
  notifyRewardAmount(e1, rewardAmount);
  
  // Determine the amount of rewards earned over the period
  mathint rewardsEnv1Before = earned(e1, user);
  withdraw(e2, depositAmount);
  mathint rewardsEnv2Before = earned(e2, user);

  mathint firstDurationRewards = rewardsEnv2Before - rewardsEnv1Before;

  // Reset to the initial state
  uint256 newDuration;
  setRewardsDuration(e1, newDuration) at cacheStorage;

  notifyRewardAmount(e1, rewardAmount);

  // Determine rewards earned over the period
  mathint rewardsEnv1After = earned(e1, user);
  withdraw(e2, depositAmount);
  mathint rewardsEnv2After = earned(e2, user);

  mathint newDurationRewards = rewardsEnv2After - rewardsEnv1After;

  assert newDurationRewards > firstDurationRewards => 
    newDuration < initialDuration, "If reward over time increased then the duration must be shorter";
  // assert newDurationRewards < firstDurationRewards => 
  //   newDuration > initialDuration, "If reward over time decreased, then the duration must be longer";
}

// @audit-ok
rule rewardPerTokenReturnsExpected() {
  env e;
  mathint result = rewardPerToken(e);
  mathint rewardPerTokenStoredResult = rewardPerTokenStored();

  mathint increaseRewardPerToken = (rewardRate() * (lastTimeRewardApplicable(e) - updatedAt()) * oneEther()) / totalSupply();

  assert totalSupply() == 0 ? 
    result == rewardPerTokenStoredResult :
    result == rewardPerTokenStoredResult + increaseRewardPerToken;
}

// @audit-ok
rule earnedReturnsExpected() {
  env e; address user;
  mathint expectedRewardIncrease = balanceOf(user) * (rewardPerToken(e) - userRewardPerTokenPaid(user)) / oneEther();

  assert earned(e, user) == rewards(user) + expectedRewardIncrease, "Earned not returning the expected value";
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

// @audit-ok
// If finishAt is equal to updatedAt the variable should no longer increase, unless notifyRewardAmount is called to reset the rewards and finishAt variable
rule updatedStopsIncreasingUnlessNotifyCalled() {
  env e; method f; calldataarg args;
  require e.block.timestamp > finishAt();

  mathint updatedAtBefore = updatedAt();
  require updatedAtBefore == finishAt();

  f(e, args);

  assert updatedAt() != updatedAtBefore <=> 
    f.selector == notifyRewardAmount(uint256).selector, 
    "Updated at should stop increasing when finish is reached";
}

// @audit-ok
rule selectMethodsModifyTotalSupplyAndBalance() {
  env e; method f; calldataarg args; uint256 amount;

  mathint totalSupplyBefore = totalSupply();
  mathint userBalanceBefore = balanceOf(e.msg.sender);
  f(e, args);
  mathint totalSupplyAfter = totalSupply();
  mathint userBalanceAfter = balanceOf(e.msg.sender);

  mathint totalSupplyChange = totalSupplyAfter - totalSupplyBefore;
  mathint userBalanceChange = userBalanceAfter - userBalanceBefore;

  assert totalSupplyChange == userBalanceChange, "Total supply should've changed the same amount as the user's balance";

  assert totalSupplyChange > 0 <=>  f.selector == stake(uint256).selector, "Total supply should only increase on stake";

  assert totalSupplyChange < 0 <=> f.selector == withdraw(uint256).selector, "Total supply should only decrease on withdraw";
}

////////////////////////////////////////////////////////////
// *************** High-level properties ***************  //
////////////////////////////////////////////////////////////

// @audit-ok
// This was very difficult to prove, provides some nice guarantee that another user can't affect the withdraw-ability of another user
rule userActionShouldntAffectAbilityToWithdrawTokens() {
  env e1; env e2; method f; calldataarg args; uint256 amount;

  require e1.msg.sender != e2.msg.sender;
  
  requireInvariant stakingContractSolvent();
  requireInvariant updatedAtLessEqualBlocktimestamp(e1);
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e2.msg.sender);

  globalRequires(e1);
  globalRequires(e2);

  require balanceOf(e2.msg.sender) >= amount;
  require stakingToken.balanceOf(e2.msg.sender) + amount <= max_uint256;
  require amount > 0;
  require e2.msg.value == 0;
  require e2.block.timestamp >= e1.block.timestamp;

  f(e1, args);

  earned(e2, e2.msg.sender); // Ensure a call to this can succeed, this doesn't limit the scope of the test too much as we are interested in whether another user can steal tokens from the first user

  withdraw@withrevert(e2, amount);

  assert !lastReverted, "User action shouldn't be able to affect ability to withdraw tokens";
}

rule userClaimingRewardsShouldntEffectOtherUser() {
  env e1; env e2;
  require e1.msg.sender != e2.msg.sender;
  requireInvariant stakingContractSolvent(); 
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e1.msg.sender);
  requireInvariant userRewardPerTokenPaidLessEqualRewardPerTokenStored(e2.msg.sender);

  globalRequires(e1);
  globalRequires(e2);

  require e2.block.timestamp >= e1.block.timestamp;
  require e2.msg.value == 0;

  getReward(e1);

  mathint expectedReward = earned(e2, e2.msg.sender);

  require rewardsToken.balanceOf(e2.msg.sender) + expectedReward <= max_uint256;

  require rewardsToken.balanceOf(currentContract) >= expectedReward;
  
  getReward@withrevert(e2);

  assert !lastReverted, "Users shouldn't affect other users claim to their rewards";
}


////////////////////////////////////////////////////////////
// ***************    Risk assessment    ***************  //
////////////////////////////////////////////////////////////


// @audit-ok
rule ownerShouldNeverChange() {
  env e; method f; calldataarg args;
  address ownerBefore = owner();
  f(e, args);

  assert owner() == ownerBefore, "The owner should never change";
}

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
  assert finalUserTokenBalance == initialTokenBalance, "User should have their 
  initial token balance back";
}


////////////////////////////////////////////////////////////
// ***************          Bugs         ***************  //
////////////////////////////////////////////////////////////

// If user stakes before round start they will receive an outsized amount of rewards compared to other users. This is because the rewardPerTokenStored = 0 in an initial state, then when notifyRewardAmount is called it will set rewardPerTokenStored to an appropriate value. Then finally when the user updates their position it will calculate their rewards per token to be: rewardPerToken() - 0; resulting in a large amount of rewards
rule bugUserGetsAnOutsizedAmountOfRewardsIfStakingBeforeStart() {
  env env1; env env2; env env3; uint256 amount;

  globalRequires(env1);
  globalRequires(env2);
  require env1.msg.sender != env2.msg.sender;
  require env1.block.timestamp >= finishAt();
  require env2.block.timestamp == env1.block.timestamp;
  require env3.block.timestamp > env2.block.timestamp;

  // This should be the initial state before a round start
  require rewardPerToken(env1) == 0;

  stake(env1, amount);
  // This should be the initial reward per token paid for the user if rewardPerToken isn't set
  assert userRewardPerTokenPaid(env1.msg.sender) == 0;

  uint256 rewardAmount;

  notifyRewardAmount(env1, rewardAmount);
  stake(env2, amount); // Second user stakes

  // Update rewards for both users, using a block.timestamp in the future
  updateRewardHelper(env3, env1.msg.sender);
  updateRewardHelper(env3, env2.msg.sender);

  mathint rewardDiff = rewards(env1.msg.sender) - rewards(env2.msg.sender);
  
  // Using this assertion so that Certora generates a counter-example demonstrating an outsized increase in rewards
  assert rewardDiff < 5 * oneEther(), "This assertion generates a counter-example highlighting an outsized difference in rewards";

  // Previously was doing the below assertion
  // assert rewards(env1.msg.sender) - rewards(env2.msg.sender);
}

////////////////////////////////////////////////////////////
// ***************        Helpers        ***************  //
////////////////////////////////////////////////////////////

// I imagine there is a better way to achieve this, couldn't find it though
definition oneEther() returns mathint =
  1000000000000000000;

definition ownerOnlyMethods(method f) returns bool =
  f.selector == setRewardsDuration(uint256).selector ||
  f.selector == notifyRewardAmount(uint256).selector;

definition userRewardUpdatingMethods(method f) returns bool =
  f.selector == getReward().selector ||
  f.selector == withdraw(uint256).selector ||
  f.selector == stake(uint256).selector ||
  f.selector == updateRewardHelper(address).selector;

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