# Certora Staking Competition Solution

This repository contains the solution for the Certora & TheSecureum workshop competition aimed at creating a .spec file using Certora Verification Language (CVL). The .spec file is aimed at verifying properties for the StakingRewards.sol contract.

For the judging in the competition Certora introduced 21 variations of the StakingRewards contract that each introduced a unique bug. The competition's judging criteria focused on whose specification file detected the most bugs. Additionally, discovering real bugs within the contract could earn extra points.

## StakingRewards Contract Overview

The `StakingRewards` contract is a Solidity implementation of a staking and rewards system. Users can stake the `stakingToken` and receive rewards in another token (`rewardsToken`). The contract keeps track of the total staked tokens, individual user balances, and rewards distribution. It also supports updating reward rates and durations.

Key functionalities include:

- Staking tokens by users
- Withdrawing staked tokens by users
- Calculating and claiming rewards for users
- Setting reward duration by the contract owner
- Notifying reward amounts by the contract owner

## Repository Structure

- `StakingRewards.sol`: The Solidity source code file for the "StakingRewards" contract.
- `StakingRewards.spec`: The .spec file written in CVL for the "StakingRewards" contract.
- `StakingRewards.sh`: A script to send the files to Certora's servers for verification.

# Comprehensive list of all properties tested

## Valid states

- Total supply is the sum of all the balances
- `updatedAt` should only ever increase
- `finishAt` is set it should always be greater than or equal to the block.timestamp
- If finishAt is zero, then updated At must be 0
- `updatedAt` less than or equal to block.timestamp
- `updatedAt` should never exceed `lastTimeRewardApplicable`
- Staking contract is solvent and has enough stakingTokens >= totalSupply()
- `lastTimeRewardApplicable` >= updatedAt
- `userRewardPerTokenPaid` <= `rewardPerTokenStored`

## Unit tests

- User rewards stop increasing after block.timestamp > finishAt
- Reward per token stops increasing after block.timestamp > finishAt
- Reward duration can only be updated if:
  - finishAt < block.timestamp
  - setRewardsDuration was called
  - e.msg.sender == admin
- `updateReward` should update rewardPerTokenStored and updatedAt
- `lastTimeRewardApplicable` should return finishAt if block.timestamp is greater than it, otherwise it should return block.timestamp
- `notifyRewardAmount` should update values
  - finishAt() = block.timestamp + duration;
  - updatedAt() = block.timestamp
  - rewardRate = updatedRewardRate
- `rewardPerToken` should stop increasing when block.timestamp > finishAt

## State transitions

- `notifyRewardAmount` should set the updated values correctly
- UpdatedAt should only increase
- If a user's rewards or userRewardPerTokenPaid is updated, then stake, withdraw or getReward were called. They are also updated to the expected values.
- `finishAt` only updatable by `notifyRewardAmount`
- If rewardPerTokenStored or updatedAt was updated, then stake, withdraw, getReward or notifyRewardAmount were called
- A user's userRewardPerTokenPaid should only ever increase
- Anti-monotinicity: If user's stakingToken balance decreases, escrow balance should increase
  - If escrow balance decreases, user's balance should increase
- `earned` should return the expected value
- `rewardPerToken` should return the expected value
- Claiming rewards should reset reward state and transfer rewards to user
- `rewardPerToken` and `updatedAt` only updated by select methods and set to expected values

## Variable transitions

- A users claimable rewards should be reset on claim
- `updatedAt` should stop increasing when finishAt < block.timestamp
- `notifyRewardAmount` sets values to expected
- `finishAt` only updated by `notifyRewardAmount`
- Reward duration can only be updated through; setRewardDuration, the caller is the owner and finishAt < block.timestamp
- Select methods increase totalSupply, select methods decrease totalSupply
- `updatedAt` stops increasing after it exceeds `finishAt()` unless `notifyRewardAmount` is called
- `rewardPerToken` should only ever increase
- `userRewardPerTokenPaid` should only increase
- `rewardRate` only updated by `notifyRewardAmount`

## High-level properties

- Another user's action shouldn't affect another user's ability to withdraw their tokens
- A user claiming rewards shouldn't affect other user's claiming rewards
- `stake` should revert when trying to stake 0 token
- `stake` should revert when trying to deposit more than the user's balance
- `withdraw` should revert when trying to withdraw 0 tokens
- `withdraw` should revert when trying to withdraw more than the user's balance
- Notify reward amount should revert if:
  - The updated reward amount will equal 0
  - There isn't enough contract balance to handle the new rewards

## Risk assessment

- Owner should never change
- Admin only methods should revert when calling from non-admin account
- A user should always be able to remove their staking tokens and get the same amount back

## Real bugs

- If a user stakes before notifyRewardAmount is called, they will earn an outsized amount of rewards compared to other users
