// SPDX-License-Identifier: MIT
pragma solidity ^0.8;

import "../../StakingRewards.sol";

contract StakingRewardsHarness is StakingRewards {
    constructor(
        address _stakingToken,
        address _rewardToken
    ) StakingRewards(_stakingToken, _rewardToken) {}

    // ! Bug contract flips the min return
    function _min(uint x, uint y) private pure override returns (uint) {
        // return x <= y ? x : y;
        return x <= y ? y : x;
    }
}
