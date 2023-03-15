// SPDX-License-Identifier: MIT
pragma solidity ^0.8;

import "../StakingRewards.sol";

contract StakingRewardsHarness is StakingRewards {
    constructor(
        address _stakingToken,
        address _rewardToken
    ) StakingRewards(_stakingToken, _rewardToken) {}

    function rewardTransferTest(address user, uint amount) external {
        rewardsToken.transfer(user, amount);
    }

    /**
     * This method returns what the updated reward rate will be if calling the notifyRewardRate method with the supplied amount parameter.
     * @param _amount The amount to calculate the new reward rate with
     */
    function getNotifyUpdatedRewardRate(
        uint _amount
    ) external view returns (uint256 updatedRewardRate) {
        if (block.timestamp >= finishAt) {
            updatedRewardRate = _amount / duration;
        } else {
            uint remainingRewards = (finishAt - block.timestamp) * rewardRate;
            updatedRewardRate = (_amount + remainingRewards) / duration;
        }
    }
}
