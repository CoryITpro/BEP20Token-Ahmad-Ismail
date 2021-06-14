/**
 *Submitted for verification at BscScan.com on 2021-06-10
*/

/**


                              ___                  
  _______  ______ __     ___ | $$\  _______
 /       \|      \    \ | $$\| $$\ | $$$$$$ \
|  $$$$$$$| $$$$$$\$$$$\|   \| $$\| $$ | $$$|
 \$$    \ | $$ | $$ | $$| $$\| $$\|$$ | $$$ |
 _\$$$$$$\| $$ | $$ | $$| $$\| $$\|$$ $$ |  $$\
|       $$| $$ | $$ | $$| $$\| $$ \|$$    $$$\
 \$$$$$$$  \$$  \$$  \$$ \$$ \| $$ \|$$$$$$\
                                    
Telegram: https://t.me/SmileToken

If you're tired of whales buying huge amounts of tokens and then Dumping them all at one, look no further!
Finely tuned tokenomics mean that each wallet can only hold 2% of the supply at any one time, max sell at any given time is 1 BNB per transaction.


for tax fee distributions.
1- %tax in token to all holders
2- %tax to add to LP pancakeswap
3- %tax convert to bnb to custom wallet addresses owner sets
4- %tax in token to custom wallet addresses owner sets

LIQ BURNED AND OWNERSHIP RENOUNCED
2% MAX WALLET TO STOP THE WHALES
 
*/
pragma solidity ^0.8.4;

// SPDX-License-Identifier: Unlicensed

interface IBEP20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the token decimals.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Returns the token symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the token name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address _owner, address spender)
        external
        view
        returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    // Empty internal constructor, to prevent people from mistakenly deploying
    // an instance of this contract, which should be used via inheritance.
    constructor() {}

    function _msgSender() internal view returns (address) {
        return payable(msg.sender);
    }

    function _msgData() internal view returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @dev Collection of functions related to the address type
 */

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     */
    function _transferOwnership(address newOwner) internal {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

interface IPancakeRouter01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
        external
        returns (
            uint256 amountA,
            uint256 amountB,
            uint256 liquidity
        );

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (
            uint256 amountToken,
            uint256 amountETH,
            uint256 liquidity
        );

    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETH(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountToken, uint256 amountETH);

    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETHWithPermit(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountToken, uint256 amountETH);

    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function quote(
        uint256 amountA,
        uint256 reserveA,
        uint256 reserveB
    ) external pure returns (uint256 amountB);

    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountOut);

    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountIn);

    function getAmountsOut(uint256 amountIn, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);

    function getAmountsIn(uint256 amountOut, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);
}

// File: contracts\interfaces\IPancakeRouter02.sol

interface IPancakeRouter02 is IPancakeRouter01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountETH);

    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

interface IPancakeFactory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB)
        external
        view
        returns (address pair);

    function allPairs(uint256) external view returns (address pair);

    function allPairsLength() external view returns (uint256);

    function createPair(address tokenA, address tokenB)
        external
        returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;

    function INIT_CODE_PAIR_HASH() external view returns (bytes32);
}


interface IPancakePair {
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
    event Transfer(address indexed from, address indexed to, uint256 value);

    function name() external pure returns (string memory);

    function symbol() external pure returns (string memory);

    function decimals() external pure returns (uint8);

    function totalSupply() external view returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 value) external returns (bool);

    function transfer(address to, uint256 value) external returns (bool);

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);

    function PERMIT_TYPEHASH() external pure returns (bytes32);

    function nonces(address owner) external view returns (uint256);

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint256);

    function factory() external view returns (address);

    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves()
        external
        view
        returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );

    function price0CumulativeLast() external view returns (uint256);

    function price1CumulativeLast() external view returns (uint256);

    function kLast() external view returns (uint256);

    function mint(address to) external returns (uint256 liquidity);

    function burn(address to)
        external
        returns (uint256 amount0, uint256 amount1);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;

    function skim(address to) external;

    function sync() external;

    function initialize(address, address) external;
}


contract SmileToken is Context, IBEP20, Ownable {
    using Address for address;

    mapping(address => uint256) private _rOwned;
    mapping(address => uint256) private _tOwned;
    mapping(address => mapping(address => uint256)) private _allowances;

    mapping(address => bool) private _isExcludedFromFee;
    mapping(address => bool) public _isBlacklisted;
    
    mapping(address => uint256) public _extraBnbRecievers;
    mapping(address => uint256) public _extraTokenRecievers;
    
    address[] private _extraBnbAddress;
    address[] private _extraTokenAddress;
    
    mapping(uint256 => uint256) public _penaltyRules;

    address[] private _excluded;

    uint256 private constant MAX = ~uint256(0);
    bool private _inSwapAndLiquify;
    bool private _penaltiesEnabled;
    uint256 private constant _tTotal = 1 * 10**12 * 10**8; // 1 trillion
    
    uint256 private _rTotal = (MAX - (MAX % _tTotal));
    uint256 private _tFeeTotal;
    
    uint256 private _liquiditySplitCeiling = 1 * 10**10 * 10**8;
    
    /**
     * @dev Initial Fees
     * 
     * 1. Tax Fee: 1%
     * 2. LP Fee: 1%
     */
     
    uint256 public _taxFee = 1;
    uint256 public _liquidityFee = 1;

    // Fee Backup
    uint256 public _previousTaxFee = _taxFee;
    uint256 public _previousLiquidityFee = _liquidityFee;
    
    /**
     * @dev Initial Settings
     * 
     * 1. Pancakeswap Router Address for BSC mainnet: 0x10ED43C718714eb63d5aA57B78B54704E256024E, 
     *                               for BSC Testnet: 0xD99D1c33F9fC3444f8101754aBC46c52416550D1
     * 2. Wallet Token Limit: 1%
     * 3. Wallet Buy Limit: 1%
     * 4. Wallet Sell Limit: 1%
     */
    
    address private _pancakeswapRouterAddress = 0xD99D1c33F9fC3444f8101754aBC46c52416550D1;
    uint256 private _maxWallet = _tTotal / 10**2 * 1;
    uint256 private _maxSell = _tTotal / 10**2 * 1;
    uint256 private _maxBuy = _tTotal / 10**2 * 1;
    
    // PancakeSwap Router Address
    // PancakeFactory address
    address _pancakeFactory = 0x3328C0fE37E8ACa9763286630A9C33c23F0fAd1A;

    IPancakeRouter02 public pcsV2Router;
    address public pcsV2Pair;

    string private _name = "DontbuyToken";
    string private _symbol = "DONTBUY";
    uint8 private _decimals = 8;
    uint256 private _start_timestamp = block.timestamp;
    
    event LiquiditySwapped(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );
    
    event DevTokensSwapped(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 ethSent,
        address devWallet
    );

    constructor() {
        _rOwned[_msgSender()] = _rTotal;
        _isExcludedFromFee[owner()] = true;
        _isExcludedFromFee[address(this)] = true;
        _isExcludedFromFee[_pancakeFactory] = true;

        IPancakeRouter02 _pancakeswapV2Router =
            IPancakeRouter02(_pancakeswapRouterAddress);
        // Create a uniswap pair for this new token
        pcsV2Pair = IPancakeFactory(_pancakeswapV2Router.factory()).createPair(
            address(this),
            _pancakeswapV2Router.WETH()
        );
        pcsV2Router = _pancakeswapV2Router;

        emit Transfer(address(0), _msgSender(), _tTotal);
    }

    modifier lockTheSwap {
        _inSwapAndLiquify = true;
        _;
        _inSwapAndLiquify = false;
    }

    function name() public view override returns (string memory) {
        return _name;
    }

    function symbol() public view override returns (string memory) {
        return _symbol;
    }

    function decimals() public view override returns (uint8) {
        return _decimals;
    }
    
    function getEquivalentValue() public view returns(uint)
    {
        IPancakePair pair = IPancakePair(pcsV2Pair);
        (uint Res0, uint Res1,) = pair.getReserves();
        
        uint bnb;
        uint nativeToken;
        
        if(pair.token0() == pcsV2Router.WETH()){
            bnb = Res0;
            nativeToken = Res1;
        }
        else {
            bnb = Res1;
            nativeToken = Res0;
        }
        
        return (bnb / nativeToken);
    }

    
    function getPairReserves() public view returns(uint, uint)
    {
        IPancakePair pair = IPancakePair(pcsV2Pair);
        (uint Res0, uint Res1, ) = pair.getReserves();
        return (Res0, Res1);
    }

    function totalSupply() public pure override returns (uint256) {
        return _tTotal;
    }

    function balanceOf(address account) public view override returns (uint256) {
        return tokenFromReflection(_rOwned[account]);
    }
    
    function isExcluded(address account) public view returns (bool) {
        return _isExcludedFromFee[account];
    }

    function transfer(address recipient, uint256 amount)
        public
        override
        returns (bool)
    {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender)
        public
        view
        override
        returns (uint256)
    {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount)
        public
        override
        returns (bool)
    {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public override returns (bool) {
        require(_allowances[sender][_msgSender()] - amount >= 0, "ERC20: transfer amount exceeds allowance");
        _transfer(sender, recipient, amount);
        _approve(
            sender,
            _msgSender(),
            _allowances[sender][_msgSender()] - amount);
        return true;
    }

    function totalFees() public view returns (uint256) {
        return _tFeeTotal;
    }
    
    function inSwapAndLiquify() public view returns (bool) {
        return _inSwapAndLiquify;
    }

    function reflect(uint256 tAmount) public {
        address sender = _msgSender();
        (uint256 rAmount, , , , , ) = _getValues(tAmount);
        _rOwned[sender] = _rOwned[sender] - rAmount;
        _rTotal = _rTotal - rAmount;
        _tFeeTotal = _tFeeTotal + tAmount;
    }

    function tokenFromReflection(uint256 rAmount)
        public
        view
        returns (uint256)
    {
        require(
            rAmount <= _rTotal,
            "Amount must be less than total reflections"
        );
        uint256 currentRate = _getRate();
        return rAmount / currentRate;
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) private {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function removeAllFee() private {
        if (_taxFee == 0 && _liquidityFee == 0) return;

        _previousTaxFee = _taxFee;
        _previousLiquidityFee = _liquidityFee;

        _taxFee = 0;
        _liquidityFee = 0;
    }
    
    function turnOffPenalties() private {
        _penaltiesEnabled = false;
    }
    
    function turnOnPenalties() private {
        _penaltiesEnabled = true;
    }

    function restoreAllFee() private {
        _taxFee = _previousTaxFee;
        _liquidityFee = _previousLiquidityFee;
    }
    
    function blacklistAddress(address account) public onlyOwner {
        _isBlacklisted[account] = true;
    }
    
    function whitelistAddress(address account) public onlyOwner {
        _isBlacklisted[account] = false;
    }

     function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) private {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");
        require(amount > 0, "Transfer amount must be greater than zero");
        
        // Addresses in Blacklist can't do buy or sell.
        require(_isBlacklisted[sender] == false && _isBlacklisted[recipient] == false, "Blacklisted addresses can't do buy or sell");

        if (
            sender != owner() &&
            recipient != owner() &&
            recipient != address(1) &&
            recipient != pcsV2Pair
        ) {
            require (
                balanceOf(recipient) + amount <= _maxWallet,
                    "Exceeds maximum wallet token amount"
            );
        } else if (
            sender != owner() &&
            recipient != owner() &&
            recipient != address(1) &&
            recipient == pcsV2Pair
        ) {
            // uint currentPriceInBNB = getEquivalentValue();
            require(amount <= _maxSell, "Transfer amount exceeds the maxTxAmount.");
            
            turnOnPenalties();
        } else if (
            sender == pcsV2Pair &&
            recipient != owner() &&
            recipient != address(1)
        ) {
            require(amount <= _maxBuy, "Transfer amount exceeds  the maxTxAmount");
            
            turnOnPenalties();
        }
        
        
        if (balanceOf(address(this)) > 0) {
            // uint currentPriceInBNB = getEquivalentValue();
            bool overLiquiditySplitCeiling = 
                /*currentPriceInBNB * */ balanceOf(address(this)) >= _liquiditySplitCeiling;
            if (
                overLiquiditySplitCeiling &&        
                !_inSwapAndLiquify && 
                sender != pcsV2Pair    
            ) {
                uint tokensToSwap = _liquiditySplitCeiling /* / currentPriceInBNB*/;
                swapAndLiquify(tokensToSwap, amount);
            }
        }

        bool takeFee = true;

        //if any account belongs to _isExcludedFromFee account then remove the fee
        if (
            _isExcludedFromFee[sender] ||
            _isExcludedFromFee[recipient]
        ) {
            takeFee = false;
        }

        if (!takeFee) removeAllFee();

        _transferStandard(sender, recipient, amount);

        if (!takeFee) restoreAllFee();
        
        turnOffPenalties();
    }

    function _transferStandard(address sender, address recipient, uint256 tAmount) private {
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getValues(tAmount);
        
        _rOwned[sender] = _rOwned[sender] - rAmount;
        _rOwned[recipient] = _rOwned[recipient] + rTransferAmount;
        
        _takeLiquidity(tLiquidity);
        
        _reflectFee(rFee, tFee);
        
        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _reflectFee(uint256 rFee, uint256 tFee) private {
        _rTotal = _rTotal - rFee;
        _tFeeTotal = _tFeeTotal + tFee;
    }

    function _getValues(uint256 tAmount) private view returns (uint256, uint256, uint256, uint256, uint256, uint256) {
        (uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getTValues(tAmount);
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee) = _getRValues(tAmount, tFee, tLiquidity, _getRate());
        return (rAmount, rTransferAmount, rFee, tTransferAmount, tFee, tLiquidity);
    }
    
    function _getAntiDumpMultiplier() private view returns (uint256) {
        uint256 time_since_start = block.timestamp - _start_timestamp;
        uint256 hour = 60 * 60;
        if (_penaltiesEnabled) {
            if (time_since_start < 1 * hour) {
                return (5);
            } else if (time_since_start < 2 * hour) {
                return (4);
            } else if (time_since_start < 3 * hour) {
                return (3);
            } else if (time_since_start < 4 * hour) {
                return (2);
            } else {
                return (1);
            }
        } else {
            return (1);
        }
    }
    
    function _getExtraFee(uint256 _transferAmount) private view returns (uint256) {
        uint256 _totalExtraFee = 0;
        for(uint256 i = 0; i < _extraTokenAddress.length; i++) {
            _totalExtraFee += _transferAmount / 10**2 * _extraTokenRecievers[_extraTokenAddress[i]];
        }
        
        for(uint256 i = 0; i < _extraBnbAddress.length; i++) {
            _totalExtraFee += _transferAmount / 10**2 * _extraBnbRecievers[_extraBnbAddress[i]];
        }
        
        return _totalExtraFee;
    }

    function _getTValues(uint256 tAmount)
        private
        view
        returns (
            uint256,
            uint256,
            uint256
        )
    {
        uint256 multiplier = _getAntiDumpMultiplier();
        uint256 _taxExtraFee = _getExtraFee(tAmount);
        uint256 tFee = tAmount / 10**2 * _taxFee * multiplier + _taxExtraFee;
        uint256 tLiquidity = tAmount / 10**2 * _liquidityFee * multiplier;
        uint256 tTransferAmount = tAmount - tFee - tLiquidity;
        return (tTransferAmount, tFee, tLiquidity);
    }

    function _getRValues(
        uint256 tAmount,
        uint256 tFee,
        uint256 tLiquidity,
        uint256 currentRate
    )
        private
        pure
        returns (
            uint256,
            uint256,
            uint256
        )
    {
        uint256 rAmount = tAmount * currentRate;
        uint256 rFee = tFee * currentRate;
        uint256 rLiquidity = tLiquidity * currentRate;
        uint256 rTransferAmount = rAmount - rFee - rLiquidity;
        return (rAmount, rTransferAmount, rFee);
    }

    function _getRate() private view returns (uint256) {
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        return rSupply / tSupply;
    }

    function _getCurrentSupply() private view returns (uint256, uint256) {
        uint256 rSupply = _rTotal;
        uint256 tSupply = _tTotal;
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (
                _rOwned[_excluded[i]] > rSupply ||
                _tOwned[_excluded[i]] > tSupply
            ) return (_rTotal, _tTotal);
            rSupply = rSupply - _rOwned[_excluded[i]];
            tSupply = tSupply - _tOwned[_excluded[i]];
        }
        if (rSupply < _rTotal - _tTotal) return (_rTotal, _tTotal);
        return (rSupply, tSupply);
    }

    function _takeLiquidity(uint256 tLiquidity) private {
        uint256 currentRate = _getRate();
        uint256 rLiquidity = tLiquidity * currentRate;
        _rOwned[address(this)] = _rOwned[address(this)] + rLiquidity;
    }

    function swapAndLiquify(uint256 contractTokenBalance, uint256 tAmount) private lockTheSwap {
        
        uint256 liquidtyPortion = contractTokenBalance;
        
        // split the contract balance into halves
        uint256 half = liquidtyPortion / 2;
        uint256 otherHalf = liquidtyPortion - half;

        // capture the contract's current BNB balance.
        // this is so that we can capture exactly the amount of ETH that the
        // swap creates, and not make the liquidity event include any ETH that
        // has been manually sent to the contract
        uint256 initialBalanceForLiquify = address(this).balance;

        // swap tokens for BNB
        swapTokensForBNB(half);

        // how much BNB did we just swap into?
        uint256 newBalanceFromLiquify = address(this).balance - initialBalanceForLiquify;

        // add liquidity to uniswap
        addLiquidity(otherHalf, newBalanceFromLiquify);

        emit LiquiditySwapped(half, newBalanceFromLiquify, otherHalf);
    
        
        uint256 initialBalanceForDevSwap = address(this).balance;
        uint256 swapPortion = 0;
        for (uint256 i = 0; i < _extraBnbAddress.length; i++) {
            swapPortion += tAmount / 10**2 * _extraBnbRecievers[_extraBnbAddress[i]];
        }
        
        swapTokensForBNB(swapPortion);
        
        uint256 swapBalanceReceived = address(this).balance - initialBalanceForDevSwap;
        
        TransferExtenBNB(swapBalanceReceived);
        TransferExtenTokens(tAmount);
        
        // emit DevTokensSwapped(devPortion, devBalanceReceived, totalDevBalanceToSend, developmentWalletAddress);
    }

    function swapTokensForBNB(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = pcsV2Router.WETH();

        _approve(address(this), address(pcsV2Router), tokenAmount);

        // make the swap
        pcsV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        // approve token transfer to cover all possible scenarios
        _approve(address(this), address(pcsV2Router), tokenAmount);

        // add the liquidity
        pcsV2Router.addLiquidityETH{value: ethAmount}(
            address(this),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            owner(),
            block.timestamp
        );
    }
    
    function TransferExtenBNB(uint256 amount) private {
        uint256 _externTokens = 0;
        uint256 _sentBnb = 0;
        for (uint256 i = 0; i < _extraBnbAddress.length; i++) {
            _externTokens += _extraBnbRecievers[_extraBnbAddress[i]];
        }
        
        for (uint256 i = 0; i < _extraBnbAddress.length; i++) {
            if (i == _extraBnbAddress.length - 1) {
                payable(_extraBnbAddress[i]).transfer(amount - _sentBnb);
            } else {
                uint256 bnbTransferForEach = (_extraBnbRecievers[_extraBnbAddress[i]] / _externTokens) * amount;
                _sentBnb += bnbTransferForEach;
                payable(_extraBnbAddress[i]).transfer(bnbTransferForEach);
            }
        }
    }
    
    function TransferExtenTokens(uint256 tAmount) private {
        for (uint256 i = 0; i < _extraTokenAddress.length; i++) {
            _tOwned[_extraTokenAddress[i]] += tAmount / 10**2 * _extraTokenRecievers[_extraTokenAddress[i]];
        }
    }

    receive() external payable {}
    
    /**********************************
    *  _____________________________  *
    * ||                           || *
    * ||   UPGRADES WITH CORY-IT   || *
    * ||___________________________|| *
    *                                 *
    **********************************/

    /**
     * @dev Change PancakeSwap Router Address
     * 
     * @param _newPscAddress: new PancakeSwap Router Address
     */
    function ChangePancakeSwapRouterAddress(address _newPscAddress) public onlyOwner {
        require(_newPscAddress != address(0), "PancakeSwap router address is not zero address");
        require(_newPscAddress.isContract() == true, "PancakeSwap router address is not payable wallet address");
        
        _pancakeswapRouterAddress = _newPscAddress;
        IPancakeRouter02 _pancakeswapV2Router = IPancakeRouter02(_pancakeswapRouterAddress);
        pcsV2Pair = IPancakeFactory(_pancakeswapV2Router.factory()).createPair(
            address(this),
            _pancakeswapV2Router.WETH()
        );
        pcsV2Router = _pancakeswapV2Router;
    }
    
    /**
     * @dev Change Max Token Limit per Wallet.
     * 
     * @param _limitDecimals: decimal value to represent percentage below 100
     * @param _percent: percent number
     * 
     * e.g. 0.0013% : _limitDecimals = 6, _percent = 13
     */
    function changeMaxTokenLimitPerWallet(uint256 _limitDecimals, uint256 _percent) public onlyOwner {
        require(_limitDecimals < 17, "Limit percentage decimals should be below 17");
        _maxWallet = ((_tTotal / 10**2) / 10**_limitDecimals) * _percent;
    }
    
    /**
     * @dev Change Max Token Sell Limit
     * 
     * @param _limitDecimals: decimal value to represent percentage below 100
     * @param _percent: percent number
     * 
     * e.g. 0.0013% : _limitDecimals = 6, _percent = 13
     */
    function changeMaxTokenSellLimit(uint256 _limitDecimals, uint256 _percent) public onlyOwner {
        require(_limitDecimals < 17, "Limit percentage decimals should be below 17");
        _maxSell = ((_tTotal / 10**2) / 10**_limitDecimals) * _percent;
    }
    
    /**
     * @dev Change Max Token Buy Limit
     * 
     * @param _limitDecimals: decimal value to represent percentage below 100
     * @param _percent: percent number
     * 
     * e.g. 0.0013% : _limitDecimals = 6, _percent = 13
     */
    function changeMaxTokenBuyLimit(uint256 _limitDecimals, uint256 _percent) public onlyOwner {
        require(_limitDecimals < 17, "Limit percentage decimals should be below 17");
        _maxBuy = ((_tTotal / 10**2) / 10**_limitDecimals) * _percent;
    }
    
    /**
     * @dev Add Extra Token Receivers
     * 
     * @param _receiver: wallet addresses owner want to send bnb from swap
     * @param _percentage: percentage to swap with bnb
     */
    function addExtraTokenReceivers(address _receiver, uint256 _percentage) public onlyOwner {
        require(_percentage >= 0, "Percentage should be even or greater than 0");
        require(_receiver != address(0), "Cannot add zero address as extra receiver");
        require(_receiver.isContract() == false, "Cannot set contract as extra receiver");
        
        _extraTokenRecievers[_receiver] = _percentage;
        _extraTokenAddress.push(_receiver);
    }
    
    /**
     * @dev Delete a extra token receiver
     * 
     * @param _receiver: wallet address owner want to send bnb from swap
     */
    function deleteExtraTokenReceivers(address _receiver) public onlyOwner {
        require(_receiver != address(0), "Cannot add zero address as extra receiver");
        require(_receiver.isContract() == false, "Cannot set contract as extra receiver");
        
        _extraTokenRecievers[_receiver] = 0;
    }
    
    /**
     * @dev Add Extra BNB Receivers
     * 
     * @param _receiver: wallet addresses owner want to send bnb from swap
     * @param _percentage: percentage to swap with bnb
     */
    function addExtraBNBReceivers(address _receiver, uint256 _percentage) public onlyOwner {
        require(_percentage >= 0, "Percentage should be even or greater than 0");
        require(_receiver != address(0), "Cannot add zero address as extra receiver");
        require(_receiver.isContract() == false, "Cannot set contract as extra receiver");
        
        _extraBnbRecievers[_receiver] = _percentage;
        _extraBnbAddress.push(_receiver);
    }
    
    /**
     * @dev Delete a extra bnb receiver
     * 
     * @param _receiver: wallet address owner want to send bnb from swap
     */
    // function deleteExtraBNBReceivers(address _receiver) public onlyOwner {
    //     require(_receiver != address(0), "Cannot add zero address as extra receiver");
    //     require(_receiver.isContract() == false, "Cannot set contract as extra receiver");
        
    //     _extraBnbRecievers[_receiver] = 0;
    // }
    
    /**
     * @dev Add penalty rules
     * 
     * @param _timegap: timestamp difference from buy and sell
     * @param _percentage: penalty value from owner
     */
    function addPenaltyRule(uint256 _timegap, uint256 _percentage) public onlyOwner {
        require(_timegap > 0, "Min hour is 1");
        require(_timegap <= 4, "Max hour is 4");
        
        _penaltyRules[_timegap] = _percentage;
    }
    
    /**
     * @dev Delete penalty rules
     * 
     * @param _timegap: timestamp difference from buy and sell
     */
    // function deletePenaltyRule(uint256 _timegap) public onlyOwner {
    //     require(_timegap <= 4, "Max hour is 4");
        
    //     _penaltyRules[_timegap] = 100;
    // }
    
    /**
     * @dev Change TaxFee
     * 
     * @param _percentage: new TaxFee percentage
     */
    function changeTaxFee(uint8 _percentage) public onlyOwner {
        require(_percentage > 0, "TaxFee must be greater zero");
        require(_percentage < 10, "TaxFee must be smaller that 10");
        
        _taxFee = _percentage;
        _previousTaxFee = _taxFee;
    }
    
    /**
     * @dev Change Liquidity Fee
     * 
     * @param _percentage: new TaxFee percentage
     */
    function changeLiquidityFee(uint8 _percentage) public onlyOwner {
        require(_percentage > 0, "Liquidity Fee must be greater zero");
        require(_percentage < 10, "Liquidity Fee must be smaller than 10");
        
        _liquidityFee = _percentage;
        _previousLiquidityFee = _liquidityFee;
    }
}
