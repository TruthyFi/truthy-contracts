// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {IOutcomeToken} from "./interfaces/IOutcomeToken.sol";

contract OutcomeToken is IOutcomeToken, Ownable, ERC20 {
    constructor(string memory name, string memory symbol) ERC20(name, symbol) Ownable(_msgSender()) {}

    function mint(address to, uint256 amount) external onlyOwner {
        _mint(to, amount);
    }

    function burn(address from, uint256 amount) external onlyOwner {
        _burn(from, amount);
    }
}
