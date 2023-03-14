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
    lastTimeRewardApplicable()      returns (uint256)   envfree
    rewardPerToken()                returns (uint256)   envfree
    earned(address)                 returns uint256     envfree
    stake(uint256)
    withdraw(uint256)
    getReward(address)
    setRewardsDuration(uint256)
    notifyRewardAmount(uint256)
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
invariant finishAtGreaterThanBlocktimestamp(env e)
  // Finish at is initialized at 0, so have to skip this pre-condition
  finishAt() != 0 => finishAt() >= e.block.timestamp
  {
    preserved with (env e1) {
      // Ensures that a parametric method doesn't have a lower block.timestamp than the pre-hook
      require e1.block.timestamp >= e.block.timestamp;
    }
  }

invariant updatedAtGreaterLessBlocktimestamp(env e)
  updatedAt() <= e.block.timestamp

// invariant updatedAtBlocktimestamp(env e) 
//   updatedAt() <= e.block.timestamp

// *** Unit test

rule updatedAtShouldOnlyIncrease(method f, env e, calldataarg args) {
  mathint updatedAtBefore = updatedAt();

  // Safe assumption
  require updatedAtBefore >= e.block.timestamp;
  require finishAt() >= e.block.timestamp;

  f(e, args);
  mathint updatedAtAfter = updatedAt();

  assert updatedAtAfter >= updatedAtBefore, "Updated at should only ever increase";
}

rule userRewardsStopIncreasingAfterRewardExpiry(env e) {
  address user;
  require user == e.msg.sender;

  mathint earned1 = earned(user);

  // Simplifies rule setup, otherwise would need to require a lot more
  require earned1 > 0;
  // Ensure the reward duration has expired
  require e.block.timestamp >= finishAt();

  mathint earned2 = earned(user);

  assert earned1 == earned2, 
    "User's earned rewards should stop increasing after reward duration expires";
}

// *** OK

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

// *** HELPERS

function globalRequires(env e) {
  require e.msg.sender != currentContract;
  require e.msg.sender != rewardsToken;
  require e.msg.sender != stakingToken;
  require rewardsToken != stakingToken;
  require stakingToken != currentContract;
  require rewardsToken != currentContract;

  requireInvariant totalSupplyIsSumOfBalances();
}