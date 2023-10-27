// member group id
const MEMBER_GROUP_DEFAULT	= 0;
const MEMBER_GROUP_GUEST	= -1;
const MEMBER_GROUP_PREPAID	= -2;
const MEMBER_GROUP_POSTPAID	= -3;
const MEMBER_GROUP_OFFER	= -4;
const MEMBER_GROUP_FREE 	= -5;

// order payment method
const PAY_METHOD_CASH 				= 0;
const PAY_METHOD_BALANCE 			= 1;
const PAY_METHOD_CARD 				= 2;
const PAY_METHOD_COIN 				= 3;
const PAY_METHOD_CASH_FOR_OFFER 	= 10;
const PAY_METHOD_BALANCE_FOR_OFFER 	= 11;
const PAY_METHOD_CARD_FOR_OFFER 	= 12;
const PAY_METHOD_COIN_FOR_OFFER 	= 13;
const PAY_METHOD_CASH_FOR_PC_TIME 	= 20;
const PAY_METHOD_BALANCE_FOR_PC_TIME= 21;
const PAY_METHOD_CARD_FOR_PC_TIME 	= 22;
const PAY_METHOD_CASH_FOR_BOOKING	= 30;
const PAY_METHOD_BALANCE_FOR_BOOKING= 31;
const PAY_METHOD_CARD_FOR_BOOKING	= 32;

// order status
const ORDER_STATUS_PENDING 			= 1;
const ORDER_STATUS_DONE 			= 2;
const ORDER_STATUS_CANCEL 			= 3;

const GAME_TYPE_NORMAL				= 1;
const GAME_TYPE_EPIC				= 2;
const GAME_TYPE_BATTLE				= 3;
const GAME_TYPE_ORIGIN				= 4;
const GAME_TYPE_STEAM				= 5;
const GAME_TYPE_RIOT				= 6;
const GAME_TYPE_ROCKSTAR			= 7;
const GAME_TYPE_UPLAY				= 8;
const GAME_TYPE_MAILRU				= 9;
const GAME_TYPE_WINAPP				= 10;

var thePCStatus = { member_account: ''};
var theLockScreenPassword = '';
var theWssLogined = false;
var theClientStatusInitialized = false; // when first wss connected, received client_status package from idc.
var theLastWindowSize = '';
var theMonitorTurnOffStartTime = 0;
var theIsHomeVersion = false;

// times
var theIdleMonitorTimerId = null;
var theIdleMiningTimerId = null;
var theCountDownIntervalId = null;
var theQueryRunGameIdsIntervalId = null;
var theMonitorTurnOffIntervalId = null;
var theAvailableOffers = [];
var theGameTrackerInterval = null;

var	theHome = new Home();
var	theTax = new Tax();
var	theShop = new Shop();
var	theGameList = new GameList();
var	theEvents = new Events();
var	theRank = new Rank();

// avoid multiple submit
var _timer = {};
function delay_execute(fn) {
	if (_timer[fn]) {
		return false
	}

	_timer[fn] = window.setTimeout(function() {
		fn();
		window.setTimeout(function(){
			window.clearTimeout(_timer[fn]);
			delete _timer[fn];
		}, 1000);
	}, 300);

	return false;
}


///////////////////////////////////// share functions  ////////////////////////////////////////////
Number.prototype.zeroPad = Number.prototype.zeroPad ||
	function(base){
		var nr = this, len = (String(base).length - String(nr).length)+1;
		return len > 0? new Array(len).join('0')+nr : nr;
	};

function toFixed2(data)
{
	var v = parseFloat(data);
	return v.toFixed(2);
}

function toLowerCase(data)
{
	return data.toLowerCase();
}

function format_time(seconds)
{
	var hours = parseInt(seconds / 3600);
	var mins = parseInt((seconds % 3600) / 60);
	var secs = seconds % 60;
	var days = parseInt(hours / 24);

	var message = hours.toString() + ":" + mins.zeroPad(10) + ":" + secs.zeroPad(10);
	if (days > 0) {
		hours = hours % 24;
		message = days.toString() + ":" + hours.zeroPad(10) + ":" + mins.zeroPad(10) + ":" + secs.zeroPad(10);
	}
	return message;
}

function sha256(ascii)
{
	function rightRotate(value, amount) {
		return (value >>> amount) | (value << (32 - amount));
	};

	var mathPow = Math.pow;
	var maxWord = mathPow(2, 32);
	var lengthProperty = 'length'
	var i, j;
	var result = ''

	var words = [];
	var asciiBitLength = ascii[lengthProperty] * 8;

	var hash = sha256.h = sha256.h || [];
	var k = sha256.k = sha256.k || [];
	var primeCounter = k[lengthProperty];

	var isComposite = {};
	for (var candidate = 2; primeCounter < 64; candidate++) {
		if (!isComposite[candidate]) {
			for (i = 0; i < 313; i += candidate) {
				isComposite[i] = candidate;
			}
			hash[primeCounter] = (mathPow(candidate, .5) * maxWord) | 0;
			k[primeCounter++] = (mathPow(candidate, 1 / 3) * maxWord) | 0;
		}
	}

	ascii += '\x80'
	while (ascii[lengthProperty] % 64 - 56) ascii += '\x00'
	for (i = 0; i < ascii[lengthProperty]; i++) {
		j = ascii.charCodeAt(i);
		if (j >> 8) return;
		words[i >> 2] |= j << ((3 - i) % 4) * 8;
	}
	words[words[lengthProperty]] = ((asciiBitLength / maxWord) | 0);
	words[words[lengthProperty]] = (asciiBitLength)

	for (j = 0; j < words[lengthProperty];) {
		var w = words.slice(j, j += 16);
		var oldHash = hash;
		hash = hash.slice(0, 8);

		for (i = 0; i < 64; i++) {
			var i2 = i + j;
			var w15 = w[i - 15], w2 = w[i - 2];

			var a = hash[0], e = hash[4];
			var temp1 = hash[7]
				+ (rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25))
				+ ((e & hash[5]) ^ ((~e) & hash[6]))
				+ k[i]
				+ (w[i] = (i < 16) ? w[i] : (
						w[i - 16]
						+ (rightRotate(w15, 7) ^ rightRotate(w15, 18) ^ (w15 >>> 3))
						+ w[i - 7]
						+ (rightRotate(w2, 17) ^ rightRotate(w2, 19) ^ (w2 >>> 10))
					) | 0
				);
			var temp2 = (rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22))
				+ ((a & hash[1]) ^ (a & hash[2]) ^ (hash[1] & hash[2]));

			hash = [(temp1 + temp2) | 0].concat(hash);
			hash[4] = (hash[4] + temp1) | 0;
		}

		for (i = 0; i < 8; i++) {
			hash[i] = (hash[i] + oldHash[i]) | 0;
		}
	}

	for (i = 0; i < 8; i++) {
		for (j = 3; j + 1; j--) {
			var b = (hash[i] >> (j * 8)) & 255;
			result += ((b < 16) ? 0 : '') + b.toString(16);
		}
	}
	return result;
}

function Tax()
{
	// get sale price with tax
	this.getPriceWithTax = function(product_tax_id, price) {
		var taxs = {
			tax1_name: theSettings.tax1_name,
			tax1_percentage: theSettings.tax1_percentage,
			tax2_name: theSettings.tax2_name,
			tax2_percentage: theSettings.tax2_percentage,
			tax3_name: theSettings.tax3_name,
			tax3_percentage: theSettings.tax3_percentage,
			tax4_name: theSettings.tax4_name,
			tax4_percentage: theSettings.tax4_percentage,
			tax_included_in_price: theSettings.tax_included_in_price,
		};
		price = parseFloat(price);
		if (taxs.tax_included_in_price == 1)
			return price.toFixed(2).replace('.00', '');

		var tax_percentage = 0;
		if (product_tax_id == 1)
			tax_percentage = taxs.tax1_percentage / 100.0;
		if (product_tax_id == 2)
			tax_percentage = taxs.tax2_percentage / 100.0;
		if (product_tax_id == 3)
			tax_percentage = taxs.tax3_percentage / 100.0;
		if (product_tax_id == 4)
			tax_percentage = taxs.tax4_percentage / 100.0;

		if (tax_percentage <= 0)
			return price.toFixed(2).replace('.00', '');

		return (price * (1 + tax_percentage)).toFixed(2).replace('.00', '');
	}

	// get tax by price
	this.getTaxWithPrice = function(product_tax_id, price) {
		var taxs = {
			tax1_name: theSettings.tax1_name,
			tax1_percentage: theSettings.tax1_percentage,
			tax2_name: theSettings.tax2_name,
			tax2_percentage: theSettings.tax2_percentage,
			tax3_name: theSettings.tax3_name,
			tax3_percentage: theSettings.tax3_percentage,
			tax4_name: theSettings.tax4_name,
			tax4_percentage: theSettings.tax4_percentage,
			tax_included_in_price: theSettings.tax_included_in_price,
		};
		price = parseFloat(price);
		var tax_percentage = 0;
		if (product_tax_id == 1)
			tax_percentage = taxs.tax1_percentage / 100.0;
		if (product_tax_id == 2)
			tax_percentage = taxs.tax2_percentage / 100.0;
		if (product_tax_id == 3)
			tax_percentage = taxs.tax3_percentage / 100.0;
		if (product_tax_id == 4)
			tax_percentage = taxs.tax4_percentage / 100.0;

		if (tax_percentage <= 0)
			return 0;

		// if price include tax
		if (taxs.tax_included_in_price == 1)
			return (price / ( 1 + tax_percentage) * tax_percentage).toFixed(2);

		return (price * tax_percentage).toFixed(2);
	}
}

function is_logined()
{
	return typeof(thePCStatus.member_account) != 'undefined' && thePCStatus.member_account != null && thePCStatus.member_account.length > 0;
}


function is_member_logined()
{
	return is_logined() && thePCStatus.member_group_id >  MEMBER_GROUP_GUEST;
}


function is_locked()
{
	return ($('#page_lock').css('display') != 'none');
}


function toast(message, level)
{
	var toast_level = (typeof(level) == 'undefined' ? 'info' : level);
	var timeout = 5000;
	var extendedTimeOut = 1000;

	if (toast_level == 'warning') {
		timeout = 30000;
		extendedTimeOut = 10000;
	}

	toastr.options = {
		"closeButton": true,
		"debug": false,
		"newestOnTop": true,
		"progressBar": false,
		"positionClass": "toast-top-right",
		"preventDuplicates": false,
		"showDuration": "300",
		"hideDuration": "1000",
		"timeOut": timeout,
		"extendedTimeOut": extendedTimeOut,
		"showEasing": "swing",
		"hideEasing": "linear",
		"showMethod": "fadeIn",
		"hideMethod": "fadeOut",
		"tapToDismiss": true
	};
	toastr[toast_level](message);
}


function countdown_stop()
{
	if (theCountDownIntervalId != null) {
		clearInterval(theCountDownIntervalId);
		theCountDownIntervalId = null;
	}
}


function countdown_start()
{
	if(theSettings.license_using_billing == 0)
		return false;

	if (!is_logined())
		return false;

	countdown_stop();
	theCountDownIntervalId = setInterval(countdown, 1000);

	return true;
}


function stop_login_timers()
{
	if (theIdleMonitorTimerId != null) {
		clearTimeout(theIdleMonitorTimerId);
		theIdleMonitorTimerId = null;
	}

	if (theIdleMiningTimerId != null) {
		clearTimeout(theIdleMiningTimerId);
		theIdleMiningTimerId = null;
	}

	if (theMonitorTurnOffIntervalId != null) {
		clearInterval(theMonitorTurnOffIntervalId);
		theMonitorTurnOffIntervalId = null;
	}
}

function stop_game_timers()
{
	if (theQueryRunGameIdsIntervalId != null) {
		clearInterval(theQueryRunGameIdsIntervalId);
		theQueryRunGameIdsIntervalId = null;
	}

	if (theGameTrackerInterval != null) {
		clearInterval(theGameTrackerInterval);
		theGameTrackerInterval = null;
	}

	countdown_stop();
}

function unlock_all()
{
	CallFunction("UNLOCK 65535");
	CallFunction("DISABLEBSOD");
}

///////////////////////////////////// form submit ////////////////////////////////////////////

function homecafeid_form_submit()
{
	$('#spinner').show();
	$('#loginForm button[type="submit"]').prop('disabled', true);
	CallFunction('HOMESETCAFEID ' + $('#homecafeidForm input[name=icafe_id]').val());
}

function login_form_submit()
{
	var strUserName = $('#loginForm input[name=username]').val();
	var strPassword = $('#loginForm input[name=password]').val();

	if (strUserName.length == 0 || strPassword.length == 0)
		return;

	$('#loginForm button[type="submit"]').prop('disabled', true);
	$('#loginForm input[name=username]').prop('disabled', true);
	$('#loginForm input[name=password]').prop('disabled', true);

	var cmd = {
		action: 'member_login',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			username: strUserName,
			password: strPassword
		}
	};

	CallFunction('WSSSEND ' + JSON.stringify(cmd));

	$('#loginForm button[type="submit"]').prop('disabled', false);
	return false;
}

function show_member_register()
{
	$('#registerForm input[name=username]').val($('#loginForm input[name=username]').val());
	$('#registerForm input[name=password]').val($('#loginForm input[name=password]').val());
	show_login_page('member_register');
}

function guest_login()
{
	CallFunction('WSSSEND ' + JSON.stringify({ action: 'member_register', version: 2, type: 'request', from: 'client', target: 'wss-server', data: {} }));
}

function member_register_form_submit()
{
	$('#registerForm button[type="submit"]').prop('disabled', true);

	var member_account = $('#registerForm input[name=username]').val();
	var member_password = $('#registerForm input[name=password]').val();
	var confirm_password = $('#registerForm input[name=confirm_password]').val();

	if (member_account.length == 0)
		throw translate_string("Account is empty");

	if (member_password.length == 0)
		throw translate_string('Password is empty');

	if (member_password != confirm_password)
		throw translate_string('Inconsistent password entered twice');

	var cmd = {
		action: 'member_register',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			member_account: member_account,
			password: member_password
		}
	};

	CallFunction('WSSSEND ' + JSON.stringify(cmd));

	$('#registerForm button[type="submit"]').prop('disabled', false);
	return false;
}


function admin_exit_form_submit()
{
	$('#adminexitForm button[type="submit"]').prop('disabled', true);

	var password = $("#adminexitForm input[name=password]").val();

	var cmd = { action: 'syslog', version: 2, type: 'request', from: 'client',	target: 'wss-server', data: {event: 'ADMINEXIT'} };
	CallFunction('WSSSEND ' + JSON.stringify(cmd));

	unlock_all();
	minimize();
	$('#adminexitForm button[type="submit"]').prop('disabled', false);
	return false;
}

function lock_form_submit()
{
	$('#lockForm button[type="submit"]').prop('disabled', true);
	theLockScreenPassword = $('#lockForm input[name=password]').val();
	$('.myModalLock').modal('hide');

	CallFunction("LOCK 65535");
	CallFunction("SETWINDOWSIZE -1*-1");
	theLastWindowSize = "-1*-1";
	CallFunction("SETWINDOWTOPMOST 1");

	$('#page_lock').show();
	$('#unlockForm input[name=password]').val('');
	$('#unlockForm input[name=password]').focus();
	$('#lockForm button[type="submit"]').prop('disabled', false);

	return false;
}


function unlock_form_submit()
{
	$('#unlockForm button[type="submit"]').prop('disabled', true);
	var pwd = $('#unlockForm input[name=password]').val();
	if (pwd != theLockScreenPassword) {
		setTimeout(function() {
			sweetAlert("", translate_string("Wrong password!"), "error");
		},100);
		$('#unlockForm button[type="submit"]').prop('disabled', false);
		return false;
	}

	if(is_logined())
	{
		if (theSettings.license_show_client_mode == 'full screen') {
			CallFunction("SETWINDOWSIZE -3*-3"); // no topmost
			theLastWindowSize = "-3*-3";
			CallFunction("SETWINDOWTOPMOST 0");
		}

		if (typeof(theSettings.license_show_client_mode) == 'undefined' || theSettings.license_show_client_mode == 'maximized') {
			CallFunction("SETWINDOWSIZE -2*-2");
			theLastWindowSize = "-2*-2";
		}

		if (theSettings.license_show_client_mode == 'minimized') {
			CallFunction("SETWINDOWSIZE -2*-2");
			theLastWindowSize = "-2*-2";
			CallFunction("HIDEWINDOW");
		}

		/*
			TASKMGR  = 0x01,	// disable task manager (Ctrl+Alt+Del)
			TASKKEYS = 0x02,	// disable task keys (Alt-TAB, etc)
			TASKBAR  = 0x04,	// disable task bar
			LOGOFF   = 0x08,	// disable task bar
			WINKEYS	 = 0x10,	// disable windows keys
		*/

		CallFunction("UNLOCK 3"); // unlock alt+tab after login, user want to switch in game
		if(theSettings.license_show_client_mode != 'full screen')
			CallFunction("UNLOCK 4"); // only enable taskbar
	}

	$('#page_lock').hide();
	$('#unlockForm button[type="submit"]').prop('disabled', false);

	return false;
}

function minimize()
{
	CallFunction("SETWINDOWSIZE -2*-2");
	theLastWindowSize = "-2*-2";
	CallFunction("HIDEWINDOW");
}

function feedback_form_submit()
{
	$('#feedbackForm button[type="submit"]').prop('disabled', true);

	var subject = $('#feedbackForm input[name=subject]').val();
	var message = $('#feedbackForm textarea[name=message]').val();

	if (subject.length == 0) {
		sweetAlert("", translate_string("Subject can not be empty!"), "error");
		$('#feedbackForm button[type="submit"]').prop('disabled', false);
		return false;
	}

	if (message.length == 0) {
		sweetAlert("", translate_string("Message can not be empty!"), "error");
		$('#feedbackForm button[type="submit"]').prop('disabled', false);
		return false;
	}

	var cmd = {
		action: 'customer_feedback',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			member_account: thePCStatus.member_account,
			subject: subject,
			message: message
		}
	};

	CallFunction('WSSSEND ' + JSON.stringify(cmd));
	toast(translate_string("Your feedback has been sent"));
	$('.myModalFeedback').modal('hide');

	$('#feedbackForm button[type="submit"]').prop('disabled', false);
	return false;
}


function change_password_form_submit()
{
	$('#passwordForm button[type="submit"]').prop('disabled', true);

	var old_password = $("#passwordForm input[name=old_password]").val();
	var new_password = $("#passwordForm input[name=new_password]").val();
	var confirm_password = $("#passwordForm input[name=confirm_password]").val();

	if(old_password == '')
	{
		sweetAlert("", translate_string("Old password can not be empty!"), "error");
		$('#passwordForm button[type="submit"]').prop('disabled', false);
		return false;
	}
	if(new_password == '')
	{
		sweetAlert("", translate_string("New password can not be empty!"), "error");
		$('#passwordForm button[type="submit"]').prop('disabled', false);
		return false;
	}
	if(confirm_password == '')
	{
		sweetAlert("", translate_string("Confirm password can not be empty!"), "error");
		$('#passwordForm button[type="submit"]').prop('disabled', false);
		return false;
	}
	if(new_password != confirm_password)
	{
		sweetAlert("", translate_string("The new password and confirm password do not match!"), "error");
		$('#passwordForm button[type="submit"]').prop('disabled', false);
		return false;
	}

	var data = {
		action:'member_change_password',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			old_password: old_password,
			new_password: new_password,
			member_id: thePCStatus.member_id
		}
	};

	CallFunction("WSSSEND " + JSON.stringify(data));
	$('#passwordForm button[type="submit"]').prop('disabled', false);
	return false;
}


function confirm_checkout_submit()
{
	if (theIsHomeVersion) {
		var cmd = {
			action: 'request_checkout',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'wss-server',
			data: {
				member_recent_played: theGameList.member_recent_played
			}};
		CallFunction('WSSSEND ' + JSON.stringify(cmd));

		process_wss_package({ action: 'client_status', version: 2, type: 'request', from: 'wss-server', target: 'client', status: 'success', data: {client_status: { member_account: '' }}});
		return false;
	}

	$('.myModalConfirmCheckout button[type="submit"]').prop('disabled', true);

	$('.myModalConfirmCheckout').modal('hide');

	if (!theWssLogined) {
		toast(translate_string("Cannot send checkout request, please contact admin"));
		$('.myModalConfirmCheckout button[type="submit"]').prop('disabled', false);
		return false;
	}

	if (is_logined() && (thePCStatus.member_group_id == MEMBER_GROUP_PREPAID || thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID))
		toast(translate_string("This session needs to check out from server, please contact admin."));

	var cmd = {
		action: 'request_checkout',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			member_recent_played: theGameList.member_recent_played
		}};
	CallFunction('WSSSEND ' + JSON.stringify(cmd));
	$('.myModalConfirmCheckout button[type="submit"]').prop('disabled', false);

	return false;
}

function rungame_show_dialog(game_id)
{
	theGames.forEach(function(obj) {
		if (game_id != obj.pkg_id)
			return;

		$('.myModalRunGame input[name=game_id]').val(obj.pkg_id);
		$('.myModalRunGame .modal-title').html(obj.pkg_name);
		$('.myModalRunGame').modal('show');
	})
}

function rungame_switch_to()
{
	var game_id = $('.myModalRunGame input[name=game_id]').val();
	$('.myModalRunGame').modal('hide');
	CallFunction("RUNGAME_SWITCH_TO " + game_id);
}

function rungame_terminate()
{
	var game_id = $('.myModalRunGame input[name=game_id]').val();
	$('.myModalRunGame').modal('hide');
	CallFunction("RUNGAME_TERMINATE " + game_id);
}

function game_tracker()
{
	// game api
	if (typeof(theLocalParams) != 'undefined' && typeof(theLocalParams.beta) != 'undefined' && theLocalParams.beta == 1)
		CallFunction("GAMETRACKER " + thePCStatus.member_id + " " + thePCStatus.status_pc_token);
}

///////////////////////////////////// element click events ////////////////////////////////////////////
function show_set_lockpassword_dialog()
{
	$('#lockForm input[name=password]').val('');
	$('.myModalLock').modal('show');
	document.getElementById('lockform_password').focus();
}


function checkout_click() {
	if (thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID && thePCStatus.member_group_id != MEMBER_GROUP_OFFER)
		$('.myModalConfirmCheckout').modal('show');
}

function close_click() {
	unlock_all();
	CallFunction("EXIT");
}

function customer_feedback()
{
	$('#feedbackForm input[name=subject]').val('');
	$('#feedbackForm textarea[name=message]').val('');

	$('.myModalFeedback').modal('show');
}


function audio_settings()
{
	CallFunction("RUN SndVol.exe");
}

function display_settings()
{
	CallFunction("RUN control.exe desk.cpl");
}

function mouse_settings()
{
	CallFunction("RUN control.exe main.cpl");
}

var theLastAssistSent = 0;
function send_assist()
{
	if (new Date() - theLastAssistSent >= 1000 * 300)
	{
		theLastAssistSent = new Date();
		var cmd = {
			action: 'remind',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'web',
			data: {
				pc: thePCInfo.pc_name,
				level: 'error',
				timeout: 0,
				message: 'assist'
			}
		};

		CallFunction('WSSSEND ' + JSON.stringify(cmd));
	}

	toast(translate_string("Your assist request has been sent"));
}


function change_password_click()
{
	$('#passwordForm input[name=member_account]').val(thePCStatus.member_account);
	$('#passwordForm input[name=old_password]').val('');
	$('#passwordForm input[name=new_password]').val('');
	$('#passwordForm input[name=confirm_password]').val('');

	$('.myModalChangePassword').modal('show');
}

function open_news(id)
{
	theCafeNews.forEach(function(obj) {
		if (obj.news_id == id) {
			CallFunction('RUN ' + obj.news_url);
			console.log('open news ' + obj.news_url);
		}
	});
}

function open_url(url)
{
	CallFunction('RUN ' + url);
	console.log('open url ' + url);
}

function handleQRClick(id) {
	vueCafeNews.items = vueCafeNews.items.map((item) => {
		if (item.news_id === id) {
			item.news_show_qr = false;
		}
		return item;
	});
}

function localTime(fmt, date) {
	var date = new Date();
	var options = {
		hour: 'numeric',
		minute: 'numeric',
		hour12: false,
	};
	return date.toLocaleString('en-US', options).replace("24:", "00:");;
}

function setDropdownMenu() {
	setTimeout(function () {
		$('.dropdown').mouseenter(function() {
			$(this).find('.dropdown-menu').show();
		});

		$('.dropdown').mouseleave(function() {
			$(this).find('.dropdown-menu').hide();
		});
	}, 100);
}

///////////////////////////////////// message process ////////////////////////////////////////////

// -- CLIENT start --
// 1. client wss connected
// 2. client send login package to server
// 2. server send login + settings package to client (assign to theSettings)
// 3. server send client_status package to client (assign to thePCStatus)

// -- CLIENT login --
// 1. client send member_login package to server
// 2. server send client_status package to client

// -- TIME over --
// 1. client send auto_checkout package to server (countdown())
// 2. server send client_status package to client

// -- click CHECKOUT --
// 1. client send request_checkout package to server
// 2. server send client_status package to client

// -- session start/checkout, add time, add offer, topup member, add order using balance on CP --
// 1. server send client_status package to client
function process_wss_package(packet)
{
	if(typeof(packet.action) == 'undefined' || typeof(packet.version) == 'undefined' || typeof(packet.type) == 'undefined' || typeof(packet.data) == 'undefined' || typeof(packet.from) == 'undefined' || typeof(packet.target) == 'undefined')
		return;
	
	if(packet.version != 2 || packet.target != 'client')
		return;

	if (theGameList.process_wss_package(packet))
		return;

	if (theConvertToMember.process_wss_package(packet))
		return;
	
	if (packet.action == 'member_register')
	{
		if(theSettings.license_using_billing == 0)
			return;
		$('#spinner').hide();
		$('#form-register-member button[type="submit"]').prop('disabled', false);

		if (packet.status == 'error') {
			sweetAlert("", translate_string(packet.data.message), "error");
			return;
		}

		sweetAlert("", translate_string("Succeed"), "success");

		$('.myModalRegisterMember').modal('hide');
		return;
	}

	data = packet.data;
	
	// response message
	if(packet.type == 'response'){
		
		if (packet.status == 'error') {
			$('#spinner').hide();
			if (packet.action == 'member_login') {
				show_login_page('login');
				sweetAlert("", translate_string(data.message), "error");
				return;
			}

			sweetAlert("", translate_string(data.message), "error");
			return;
		}
		
		if (packet.action == 'member_change_password') {
			sweetAlert(translate_string("Succeed"), translate_string("The password was changed successfully."), "success");
			$('.myModalChangePassword').modal('hide');
			return;
		}

		if (packet.action == 'login') {
			// after first wss connected
			if (typeof(theSettings.login_count) == 'undefined')
				theSettings.login_count = 0;

			if (theSettings.login_count == 0) {
				$('.currency').html(typeof(theSettings.currency) == 'undefined' ? '$' : theSettings.currency)

				$('#offers_div').hide();
				if (theSettings.license_using_billing == 0) {
					vueGlobal.menuButton.logout = false;
					vueGlobal.menuButton.feedback = false;
					vueGlobal.menuButton.assist = false;
					vueGlobal.menuButton.changepassword = false;
				}
				if (theSettings.license_using_billing == 1) {
					vueGlobal.menuButton.logout = true;
					vueGlobal.menuButton.feedback = true;
					vueGlobal.menuButton.assist = true;
				}
				if (!theIsHomeVersion && theSettings.license_using_billing == 1)
					$('#offers_div').show();

				if (theSettings.license_web_log_enable == 1 && typeof(theLocalParams) != 'undefined' && typeof(theLocalParams.server_ip) != 'undefined') {
					CallFunction('RUN "{tools}\\setproxy.bat" 1 "' + theLocalParams.server_ip + ':808"');
					console.log('RUN "{tools}\\setproxy.bat" 1 "' + theLocalParams.server_ip + ':808"');
				}

				if (theSettings.license_web_log_enable == 0) {
					CallFunction('RUN "{tools}\\setproxy.bat" 0 ""');
					console.log('RUN "{tools}\\setproxy.bat" 0 ""');
				}

				// first connect, set timeout for idle shutdown (don't move below codes to any where)
				if(!theIsHomeVersion && !is_logined() && theSettings.client_idle_mins > 0)
				{
					if (theIdleMonitorTimerId != null) {
						clearTimeout(theIdleMonitorTimerId);
						theIdleMonitorTimerId = null;
					}
					theIdleMonitorTimerId = setTimeout(function () {
						if (theSettings.client_idle_action.toLowerCase() == 'run') {
							console.log('RUN run.bat');
							CallFunction('RUN run.bat');
						}

						if (theSettings.client_idle_action.toLowerCase() == 'shutdown') {
							unlock_all();
							CallFunction("SHUTDOWN ONLY");
						}
					}, theSettings.client_idle_mins * 1000 * 60);
				}
			}

			theSettings.login_count ++;
			return;
		}

		if (packet.action == 'submit_order') {
			toast(translate_string('Your order submitted'));
			if (data.pay_method == 3) {
				theShop.gift_cart_clear();
				return;
			}
			theShop.cart_clear();
		}

		return; // return other response message
	}

	// reply the request message
	CallFunction('WSSSEND ' + JSON.stringify({ action: packet.action, version: 2, type: 'response', from: 'client', target: 'wss-server', status: 'success', data: {} }));
	// already has session, auto start session
	// checkout command only from CP!!
	// request message
	if(packet.action == 'admin_message'){
		toastr.options.tapToDismiss = true;
		toastr.options.timeOut = 0;
		toastr.options.extendedTimeOut = 0;
		toastr.info(translate_string('Message from admin:') + ' ' + data.message);
		CallFunction("PLAYSOUND customized/admin-message.wav admin-message.wav");
		$('#block-div').show();
		$('.toast').click(function(){
			$('#block-div').hide();
		});
		return;
	}

	if (packet.action == 'client_status') {
		$('#spinner').hide();
		// if disable billing, auto login
		if (theSettings.license_using_billing == 0 && !theClientStatusInitialized) {
			theClientStatusInitialized = true;
			guest_login();
			return;
		}

		var last_login_status = is_logined();
		var member_loan = 0;
		if (last_login_status && thePCStatus.member_loan > 0)
			member_loan = thePCStatus.member_loan;

		countdown_stop();
		thePCStatus = data.client_status;

		console.log("Current state is " + (is_logined() ? 'logined' : 'logout'));
		console.log("Previous state is " + (last_login_status ? 'logined' : 'logout'));

		var d = new Date();
		thePCStatus.login_time = parseInt((d.getTime() + d.getTimezoneOffset()*60*1000)/1000);  // UTC time
		if(thePCStatus.member_group_name == null)
		{
			if(thePCStatus.member_group_id == MEMBER_GROUP_DEFAULT)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Default');
			}

			if(thePCStatus.member_group_id == MEMBER_GROUP_GUEST)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Guest');
			}

			if(thePCStatus.member_group_id == MEMBER_GROUP_PREPAID)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Prepaid');
			}

			if(thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Postpaid');
			}

			if(thePCStatus.member_group_id == MEMBER_GROUP_FREE)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Free');
			}

			if(thePCStatus.member_group_id == MEMBER_GROUP_OFFER)
			{
				thePCStatus.member_group_desc = thePCStatus.member_group_name = translate_string('Offer');
			}
		}

		if(thePCStatus.status_connect_time_left && thePCStatus.status_connect_time_left.length > 0)
		{
			// if time left < 00:00:00
			if (thePCStatus.status_connect_time_left.charAt(0) == '-')
			{
				thePCStatus.status_connect_time_left = -1;
			}
			else
			{
				var items = thePCStatus.status_connect_time_left.split(':');
				if(items.length == 0)
					thePCStatus.status_connect_time_left = 0;
				// parseInt("08") and parseInt("09") in wke return 0, must use parseInt("08", 10)
				if(items.length == 1)
					thePCStatus.status_connect_time_left = parseInt(items[0], 10);
				if(items.length == 2)
					thePCStatus.status_connect_time_left = parseInt(items[0], 10) * 60 + parseInt(items[1], 10);
				if(items.length == 3)
					thePCStatus.status_connect_time_left = parseInt(items[0], 10) * 60 * 60 + parseInt(items[1], 10) * 60 + parseInt(items[2], 10);
			}
		}

		// postpaid show time used
		if(thePCStatus.status_connect_time_duration && thePCStatus.status_connect_time_duration.length > 0)
		{
			// if time left < 00:00:00
			var items = thePCStatus.status_connect_time_duration.split(':');
			if(items.length == 0)
				thePCStatus.status_connect_time_duration = 0;
			// parseInt("08") and parseInt("09") in wke return 0, must use parseInt("08", 10)
			if(items.length == 1)
				thePCStatus.status_connect_time_duration = parseInt(items[0], 10);
			if(items.length == 2)
				thePCStatus.status_connect_time_duration = parseInt(items[0], 10) * 60 + parseInt(items[1], 10);
			if(items.length == 3)
				thePCStatus.status_connect_time_duration = parseInt(items[0], 10) * 60 * 60 + parseInt(items[1], 10) * 60 + parseInt(items[2], 10);
		}

		// in login page
		if (!is_logined())
		{
			stop_game_timers();
			
			if(last_login_status) // after checkout
			{
				CallFunction('RUN logout.bat');
				
				// game api
				// game_tracker();

				show_login_page('login');
				theEvents.reset();

				if(theIsHomeVersion)
					return;

				// switch to icafemenu
				CallFunction("RUNGAME_SWITCH_TO 0");

				if (member_loan > 0) {
					$('.myModalMessage .modal-title').html(translate_string('Your Outstanding Bill'));
					$('.myModalMessage .modal-body p').html(translate_string('Your total outstanding bill is now {0} {1} which can be paid at the front desk.').replace('{0}', member_loan).replace('{1}', theSettings.currency));
					$('.myModalMessage').modal('show');
				}

				var client_idle_mins = (typeof(theSettings.client_idle_mins) != 'undefined' ? theSettings.client_idle_mins : 0);
				if (client_idle_mins > 0)
				{
					// action after idle time
					if (theIdleMonitorTimerId != null) {
						clearTimeout(theIdleMonitorTimerId);
						theIdleMonitorTimerId = null;
					}
					console.log('Will ' + theSettings.client_idle_action + ' after idle ' + client_idle_mins + ' minutes');
					theIdleMonitorTimerId = setTimeout(function () {

						if (theSettings.client_idle_action.toLowerCase() == 'run') {
							console.log('RUN run.bat');
							CallFunction('RUN run.bat');
						}

						if (theSettings.client_idle_action.toLowerCase() == 'shutdown') {
							unlock_all();
							console.log('Shutdown');
							CallFunction("SHUTDOWN ONLY");
						}

						if (theSettings.client_idle_action.toLowerCase() == 'reboot') {
							unlock_all();
							console.log('Reboot');
						}

						if (theSettings.client_idle_action.toLowerCase() == 'logoff') {
							unlock_all();
							console.log('Logoff');
							CallFunction("SHUTDOWN LOGOFF");
						}

						if (theSettings.client_idle_action.toLowerCase() == 'close all apps') {
							// kill all apps
							console.log('Close all apps');
							CallFunction("RUNGAME_TERMINATE 0");
						}

					}, client_idle_mins * 1000 * 60);
				}

				var pc_mining_enabled = (typeof(thePCStatus.pc_mining_enabled) != 'undefined' ? thePCStatus.pc_mining_enabled : 0);
				if (pc_mining_enabled === 1)
				{
					var client_mining_idle_mins = typeof(theSettings.client_mining_idle_mins) != 'undefined' ? theSettings.client_mining_idle_mins : 5;
					console.log("Will start miner after " + client_mining_idle_mins + " minutes");
					theIdleMiningTimerId = setTimeout(function () {
						var pc_mining_tool = (typeof(thePCStatus.pc_mining_tool) != 'undefined' ? thePCStatus.pc_mining_tool : 'nicehash');
						var pc_mining_options = (typeof(thePCStatus.pc_mining_options) != 'undefined' ? thePCStatus.pc_mining_options : '');
						CallFunction("MINER_START " + pc_mining_tool + " " + pc_mining_options);
					}, client_mining_idle_mins * 1000 * 60);
				}

				return;
			}
			
			if (theIsHomeVersion) // home version don't mining in login page
				return;

			// normal login page
			
			// show booking info
			if (typeof(thePCStatus.recent_booking) != 'undefined' && thePCStatus.recent_booking != null)
			{
				toast(translate_string("Recent booking") + ": " + thePCStatus.recent_booking, 'warning');
			}
			
			var pc_mining_enabled = (typeof (thePCStatus.pc_mining_enabled) != 'undefined' ? thePCStatus.pc_mining_enabled : 0);
			if (pc_mining_enabled == 1 && theIdleMiningTimerId == null) {
				var client_mining_idle_mins = typeof (theSettings.client_mining_idle_mins) != 'undefined' ? theSettings.client_mining_idle_mins : 5;
				console.log("Will start miner after " + client_mining_idle_mins + " minutes");
				theIdleMiningTimerId = setTimeout(function () {
					var pc_mining_tool = (typeof (thePCStatus.pc_mining_tool) != 'undefined' ? thePCStatus.pc_mining_tool : 'nicehash');
					var pc_mining_options = (typeof (thePCStatus.pc_mining_options) != 'undefined' ? thePCStatus.pc_mining_options : '');
					CallFunction("MINER_START " + pc_mining_tool + " " + pc_mining_options);
				}, client_mining_idle_mins * 1000 * 60);
			}
			return;
		}
		// end login page
		
		// already logined
		theConvertToMember.init();


		// login in & previous state is checkout & not locked
		if(!last_login_status) // from login to logined
		{
			if (theEvents.events.length == 0)
				theEvents.load_list();

			if(!theIsHomeVersion)
			{
				if (theSettings.license_show_client_mode == 'full screen') {
					CallFunction("SETWINDOWSIZE -3*-3"); // no topmost
					theLastWindowSize = "-3*-3";
					CallFunction("SETWINDOWTOPMOST 0");
				}

				if (typeof(theSettings.license_show_client_mode) == 'undefined' || theSettings.license_show_client_mode == 'maximized') {
					CallFunction("SETWINDOWSIZE -2*-2");
					theLastWindowSize = "-2*-2";
				}

				if (theSettings.license_show_client_mode == 'minimized') {
					CallFunction("SETWINDOWSIZE -2*-2");
					theLastWindowSize = "-2*-2";
					CallFunction("HIDEWINDOW");
				}
				
				/*
					TASKMGR  = 0x01,	// disable task manager (Ctrl+Alt+Del)
					TASKKEYS = 0x02,	// disable task keys (Alt-TAB, etc)
					TASKBAR  = 0x04,	// disable task bar
					LOGOFF   = 0x08,	// disable task bar
					WINKEYS	 = 0x10,	// disable windows keys
				*/
				
				CallFunction("UNLOCK 3"); // unlock alt+tab after login, user want to switch in game
				if(theSettings.license_show_client_mode != 'full screen')
					CallFunction("UNLOCK 4"); // only enable taskbar
			}
			
			CallFunction('RUN login.bat');
			if(theSettings.license_start_game_tracker ?? 0)
				CallFunction("API type=game-rank-data");

			theHome.show();
			if(theSettings.show_game_page_as_default)
				theGameList.show();

			stop_login_timers();
			
			if (theIsHomeVersion) 
			{
				theEvents.show();
			}
			else 
			{
				if (theSettings.license_save_enable)
				{
					if(is_member_logined())
						CallFunction("INIT_GAME_SAVING " + thePCStatus.member_account);
					else
						CallFunction("INIT_GAME_SAVING guest_" + thePCInfo.pc_name);
				}
			}

			// start monitoring game track for fornite/lol
			if (theGameTrackerInterval != null)
			{
				clearInterval(theGameTrackerInterval);
				theGameTrackerInterval = null;
			}
			// stop game api tracker currently
			// theGameTrackerInterval = setInterval(game_tracker, 1000 * 60 * 5);
		}
		// end from login to logined

		// already logined but wss reconnect, or topup update left time
		
		if (typeof(thePCStatus.recent_booking) != 'undefined' && thePCStatus.recent_booking != null) 
		{
			toast(translate_string("Recent booking") + ": " + thePCStatus.recent_booking, 'warning');
		}

		// now state is login in (from logined to logined)

		// don't show checkout button if not member login
		vueGlobal.menuButton.logout = false;
		if (thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID && thePCStatus.member_group_id != MEMBER_GROUP_OFFER)
			vueGlobal.menuButton.logout = true;

		// show member info
		memberInfo.member_info_name = thePCStatus.member_account.toUpperCase() + " / " + thePCStatus.member_group_name.toUpperCase();
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
		
		$('.cafe_info_member_logo').attr('src', 'icons/mg-' + (thePCStatus.member_group_id > MEMBER_GROUP_DEFAULT ? thePCStatus.member_group_id.toString() : '0') + '.png');
	
		if (theSettings.license_using_billing == 1)
		{
			theAvailableOffers = [];
			var id = 1;
			for (var i=0; i<thePCStatus.available_offers.length; i++)
			{
				var in_using = (thePCStatus.available_offers[i].product_name == thePCStatus.offer_in_using && i == 0);
				theAvailableOffers.push({
					id: id++,
					in_using: in_using,
					time_type: 'offer',
					name: thePCStatus.available_offers[i].product_name.toUpperCase(),
					total_secs: thePCStatus.available_offers[i].product_seconds,
					left_secs: (in_using ? thePCStatus.status_connect_time_left : thePCStatus.available_offers[i].member_offer_left_seconds),
					last_notify_mins: 1000,
					active: ''
				});
			}

			if (thePCStatus.member_balance_bonus_left_seconds > 0)
			{
				var in_using = (thePCStatus.offer_in_using == null || thePCStatus.offer_in_using.length == 0);
				var name = translate_string('BALANCE');
				var left_secs = in_using ? thePCStatus.status_connect_time_left : thePCStatus.member_balance_bonus_left_seconds;
				if (thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID || thePCStatus.member_group_id == MEMBER_GROUP_FREE) {
					left_secs = thePCStatus.status_connect_time_left;
				}

				theAvailableOffers.push({
					id: id++,
					in_using: in_using,
					time_type: 'balance',
					name: name,
					total_secs: thePCStatus.member_balance_bonus_left_seconds,
					left_secs: left_secs,
					last_notify_mins: 1000,
					active: ''
				});
			}

			// add total
			if (theAvailableOffers.length > 0)
			{
				var total_secs = 0;
				var left_secs = 0;
				theAvailableOffers.forEach(function(obj) {
					total_secs += obj.total_secs;
					left_secs += obj.left_secs;
				});

				theAvailableOffers.splice(0, 0, {
					id: id++,
					in_using: false,
					time_type: 'total',
					name: translate_string('TOTAL'),
					total_secs: total_secs,
					left_secs: left_secs,
					last_notify_mins: 1000,
					active: ''
				});
			}

			if (theAvailableOffers.length > 0)
			{
				theAvailableOffers[0].in_using = true;
				theAvailableOffers[0].active = 'active';
			}

			vueAvailableOffers.items = JSON.parse(JSON.stringify(theAvailableOffers));
			PetiteVue.nextTick(() => {
				ui_init();
				$('[data-toggle="tooltip"]').tooltip();
			});
			
			$('#carousel_main').carousel({ interval: false });
		}

		countdown_start();
		if (!theIsHomeVersion) {
			if (theQueryRunGameIdsIntervalId != null) {
				clearInterval(theQueryRunGameIdsIntervalId);
				theQueryRunGameIdsIntervalId = null;
			}
			query_rungame_ids();
			theQueryRunGameIdsIntervalId = setInterval(query_rungame_ids, 3000);
		}

		// show left money and bonus
		$('.member_balance_realtime').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE ? 'd-flex' : 'd-none');
		$('.member_balance_bonus_realtime').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID ? 'd-flex' : 'd-none');
		$('.member_coin_balance').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID ? 'd-flex' : 'd-none');
		$('.postpaid_pc_name').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID || thePCStatus.member_group_id == MEMBER_GROUP_FREE ? 'd-flex' : 'd-none');

		if (theSettings.license_using_billing == 1 && thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE) {
			var member_balance_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_realtime), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_balance_realtime > 1000000)
				member_balance_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_realtime / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_balance_realtime = member_balance_realtime;

			var member_balance_bonus_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_bonus_realtime), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_balance_bonus_realtime > 1000000)
				member_balance_bonus_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_bonus_realtime / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_balance_bonus_realtime = member_balance_bonus_realtime;

			var member_coin_balance = accounting.formatMoney(parseFloat(thePCStatus.member_coin_balance), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_coin_balance > 1000000)
				member_coin_balance = accounting.formatMoney(parseFloat(thePCStatus.member_coin_balance / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_coin_balance = member_coin_balance;
			
			PetiteVue.nextTick(() => {
				ui_init();
				$('[data-toggle="tooltip"]').tooltip();
			});
		}
		// end now state is login in
		return;
	}
	// end client_status

	if (packet.action == 'quit' || packet.action == 'exit') {
		unlock_all();
		CallFunction("EXIT");
		return;
	}

	if (packet.action == 'shutdown' && !theIsHomeVersion) {
		unlock_all();
		CallFunction("SHUTDOWN ONLY");
		return;
	}

	if (packet.action == 'reboot' && !theIsHomeVersion) {
		unlock_all();
		return;
	}

	if (packet.action == 'logoff' && !theIsHomeVersion) {
		unlock_all();
		CallFunction("SHUTDOWN LOGOFF");
		return;
	}

}


function OnCommand(strCmd, strParam)
{
	strParam = strParam.replace(/____@@@____/g, '\\')
	strParam = strParam.replace(/____@@____/g, '"')
	strParam = strParam.replace(/____@____/g, '\'')
	strParam = strParam.replace(/___@@@@___/g, '\r')
	strParam = strParam.replace(/___@@@@@___/g, '\n')

	if (strCmd == "CallExeDone") {
		var cols = strParam.split(' ');
		if (typeof(cols) == 'undefined')
			return;
		if (cols.length == 0)
			return;
		var action = cols[0];

		if (action == 'INIT_GAME_SAVING') {
			setTimeout(function () {
				$('input[name=search]').css({background: '#ffffff'});

				setTimeout(function () {
					$('input[name=search]').css({background: 'transparent'});
				}, 500);

			}, 500);
		}

		return;
	}

	if (strCmd == "SHOWMSG") {
		sweetAlert("", translate_string(strParam), "info");
		return;
	}

	if (strCmd == 'TOAST') {
		toast(translate_string(strParam));
		return;
	}
	
	// if wss_timeout, lock the client
	if (strCmd == 'WSS_TIMEOUT') {
		// direct to login page, allow player work when cloud server down
		// process_wss_package({ action: 'client_status', version: 2, type: 'request', from: 'wss-server', target: 'client', status: 'success', data: {client_status: { member_account: '' }}});
		return;
	}

	if (strCmd == 'WSS_LOGIN') {
		theWssLogined = true;

		$('#loginForm input[name=username]').prop('disabled', !theWssLogined);
		$('#loginForm input[name=password]').prop('disabled', !theWssLogined);
		$('#loginForm button').css({opacity: 1.0});
		return;
	}

	if (strCmd == 'WSS_LOGIN_FAILED') {
		if (!theIsHomeVersion)
			return;
		$('#spinner').hide();
		show_login_page('login');
		sweetAlert("", translate_string('Login failed'), 'error');
		return;
	}

	if (strCmd == 'WSS_DISCONNECTED') {
		theWssLogined = false;

		if (theIsHomeVersion)
			return;
		$('#loginForm input[name=username]').prop('disabled', !theWssLogined);
		$('#loginForm input[name=password]').prop('disabled', !theWssLogined);
		$('#loginForm button').css({opacity: 0.5});
		return;
	}

	if (strCmd == 'WM_DISPLAYCHANGE') {
		if (theLastWindowSize.length > 0)
			CallFunction("SETWINDOWSIZE " + theLastWindowSize);

		return;
	}

	if (strCmd == 'WSS_COMMAND') {
		var data = JSON.parse(strParam);
		process_wss_package(data);

		return;
	}

	if (strCmd == 'COVERSHOW') {
		$('#spinner').show();
		return;
	}

	if (strCmd == 'COVERHIDE') {
		$('#spinner').hide();
		return;
	}

	if (strCmd == "RUNGAME_IDS") {
		var ids = strParam.split(',');
		var html = '';
		for (var i=0; i<ids.length; i++) {

			theGames.forEach(function(obj) {
				if (obj.pkg_id == ids[i]) {
					html += ('<a class="run-game-icon" href="javascript:rungame_show_dialog(' + obj.pkg_id + ')" data-toggle="tooltip" data-placement="bottom" title="' + obj.pkg_name + '"><img src="icons/' + obj.pkg_id + '.png" onerror="this.src=\'images/default-icon.png\'"></a>');
				}
			});

		}
		$('#bottom-run-games').html(html);
		$('#bottom-run-games [data-toggle="tooltip"]').tooltip();
		return;
	}

	if (strCmd == "APIResponse") {
		var pos = strParam.indexOf(' ');
		var api_action = strParam.substr(0, pos);
		strParam = strParam.substr(pos+1);
		if(strParam.length == 0)
			return;
		var data = JSON.parse(strParam);

		if (api_action.indexOf('type=event-') >= 0) {
			theEvents.onAPIResponse(api_action, data);
			return;
		}

		if (api_action.indexOf('type=game-rank-data') >= 0) {
			if (data.result == 0) {
				sweetAlert("", translate_string(data.message), 'error');
				return;
			}
			vueHome.leaderboardItems = JSON.parse(JSON.stringify(data.rank));
			return;
		}
		return;
	}
	
	if (strCmd == "PCInfo") {
		thePCInfo = JSON.parse(strParam);
		if(!$('#page_login').is(":visible"))
			return;

		set_monitor_turn_off_timeout(thePCInfo.pc_turn_off_monitor_seconds);
		if (theIsHomeVersion)
			$('#loginForm input[name=username]').val(thePCInfo.pc_name);
		else
			$('#page_login .pc_name').html(thePCInfo.pc_name);
		
		$('#version_date').html("v. " + thePCInfo.version_date);
		
		return;
	}
}




///////////////////////////////////// UI ////////////////////////////////////////////

// <lang> No permission </lang>
// <lang> Account not exists </lang>
// <lang> Wrong password </lang>
// <lang> Operation failure </lang>
// <lang> Invalid parameter </lang>
// <lang> The password was changed successfully. </lang>
// <lang> Invalid client </lang>
// <lang> Invalid parameter </lang>
// <lang> Update client information failed </lang>
// <lang> Invalid license </lang>
// <lang> Account already exists </lang>
// <lang> Free to play </lang>
// <lang> All Games </lang>
// <lang> Favorite </lang>
// <lang> Drink </lang>
// <lang> Food </lang>
var vueGlobal = PetiteVue.reactive({
	pageType: 'Home',
	showBottom: true,
	bodyStyle: [],
	menuButton: {
		logout: true,
		feedback: true,
		assist: true,
		changepassword: false,
		convertToMember: true,
	}
});
var vueHome = PetiteVue.reactive({
	promotedItems: [],
	promotedActive: 0,
	leaderboardItems: null,
	leaderboardActive: 0,
	memberGroup: [],
	memberCurrentGroup: 0,
	memberPointValue: ""
});
var vueClasses = PetiteVue.reactive({
	items: []
});
var vueGames = PetiteVue.reactive({
	items:[],
	topFiveItems: [],
	type: 'all',
	active_class: '',
	status_pc_token: ''
});
var vueEventBanner = PetiteVue.reactive({
	event:[]
});
var vueEventsMy = PetiteVue.reactive({
	events:[]
});
var vueEventsActive = PetiteVue.reactive({
		events:[]
});
var vueEventsDetail = PetiteVue.reactive({
	events:[]
});
var vueEventButtons = PetiteVue.reactive({
	event:[]
});
var vueEventDetail = PetiteVue.reactive({
	event:[],
	members: []
});
var vueProductGroupList = PetiteVue.reactive({
	items:[],
	dropdownProductGroupList: [],
	current_group_id: -3,
});
var vueProducts = PetiteVue.reactive({
	items:[]
});
var vueOrderItems = PetiteVue.reactive({
	items:[],
	total_cost: 0,
	total_tax: 0,
	total_discount: 0,
	total_amount: 0,
	payment_method: -1,
	member_group_discount_rate: 0,
	member_group_id: 0
});
var vueGiftOrders = PetiteVue.reactive({
	items:[],
	total_amount: 0
});
var vueAvailableOffers = PetiteVue.reactive({
	items:[]
});
var vueCafeNews = PetiteVue.reactive({
	items:[]
});
var memberInfo = PetiteVue.reactive({
	member_info_name: '',
	member_balance_realtime: '',
	member_balance_bonus_realtime: '',
	member_coin_balance: '',
	postpaid_pc_name: '',
	price_per_hour: ''
});
var vueRank = PetiteVue.reactive({
	items: {
		fortnite: [],
		lol: [],
		dota2: [],
		valorant: [],
		csgo: []
	},
	active_game: "",
});
function main()
{
	if(typeof(theSettings.client_themes_front_color) != 'undefined')
	{
		document.documentElement.style.setProperty('--client_themes_front_color', theSettings.client_themes_front_color);
		document.documentElement.style.setProperty('--client_themes_front_color_90', theSettings.client_themes_front_color + 'e6');
		document.documentElement.style.setProperty('--client_themes_front_color_75', theSettings.client_themes_front_color + 'c0');
		document.documentElement.style.setProperty('--client_themes_back_color', theSettings.client_themes_back_color);
		document.documentElement.style.setProperty('--client_themes_back_color_90', theSettings.client_themes_back_color + 'e6');
		document.documentElement.style.setProperty('--client_themes_back_color_75', theSettings.client_themes_back_color + 'c0');
	}
	
	// setting the required prop for each required field
	if(typeof(theSettings.member_settings) != 'undefined')
	{
		var member_settings = JSON.parse(theSettings.member_settings);

		$('#form-convert-member input[name=account], #form-register-member input[name=account]').prop('required', member_settings.member_account == 1);
		$('#form-convert-member input[name=first_name], #form-register-member input[name=first_name]').prop('required', member_settings.member_first_name == 1);
		$('#form-convert-member input[name=last_name], #form-register-member input[name=last_name]').prop('required', member_settings.member_last_name == 1);
		$('#form-convert-member input[name=password], #form-register-member input[name=password]').prop('required', member_settings.member_password == 1);
		$('#form-convert-member input[name=confirm_password], #form-register-member input[name=confirm_password]').prop('required', member_settings.member_password == 1);
		$('#form-convert-member input[name=member_expire_time_local], #form-register-member input[name=member_expire_time_local]').prop('required', member_settings.member_expire_time_local == 1);
		$('#form-convert-member input[name=birthday], #form-register-member input[name=birthday]').prop('required', member_settings.member_birthday == 1);
		$('#form-convert-member input[name=phone], #form-register-member input[name=phone]').prop('required', member_settings.member_phone == 1);
		$('#form-convert-member input[name=email], #form-register-member input[name=email]').prop('required', member_settings.member_email == 1);

		$('#form-convert-member, #form-register-member').find('input').each(function () {
			if($(this).prop('required')){
				$(this).parents().children('label').addClass('required');
			}
		});
	}

	$('#localTime').html(localTime());
	setInterval(function() {
		$('#localTime').html(localTime());
	},1000*60);

	PetiteVue.createApp({
		mounted() {
			translate_obj($('body'));
			$('[data-toggle="tooltip"]').tooltip();
			/*// Initialising the canvas
			$('#page_games').css({'background-image': 'none'});
			var canvas = document.querySelector('canvas'),
			ctx = canvas.getContext('2d');

			// Setting the width and height of the canvas
			canvas.width = width = window.innerWidth;
			canvas.height = height = window.innerHeight;

			// Setting up the letters
			var letters = 'ABCDEFGHIJKLMNOPQRSTUVXYZABCDEFGHIJKLMNOPQRSTUVXYZABCDEFGHIJKLMNOPQRSTUVXYZABCDEFGHIJKLMNOPQRSTUVXYZABCDEFGHIJKLMNOPQRSTUVXYZABCDEFGHIJKLMNOPQRSTUVXYZ';
			letters = letters.split('');

			// Setting up the columns
			var fontSize = 10,
				columns = width / fontSize;

			// Setting up the drops
			var drops = [];
			for (var i = 0; i < columns; i++) {
			  drops[i] = 1;
			}

			// Setting up the draw function
			function draw() {
			  ctx.fillStyle = 'rgba(0, 0, 0, .1)';
			  ctx.fillRect(0, 0, width, height);
			  for (var i = 0; i < drops.length; i++) {
				var text = letters[Math.floor(Math.random() * letters.length)];
				ctx.fillStyle = '#0f0';
				ctx.fillText(text, i * fontSize, drops[i] * fontSize);
				drops[i]++;
				if (drops[i] * fontSize > height && Math.random() > .95) {
				  drops[i] = 0;
				}
			  }
			}

			// Loop the animation
			setInterval(draw, 100);*/
		}
	}).mount('body')

	// debug for tooltip
	//$('body').tooltip({selector: "[data-toggle='tooltip']", trigger: "click"});

	theIsHomeVersion = (typeof(theSettings) != 'undefined' && typeof(theSettings.enable_icafesports) != 'undefined' && theSettings.enable_icafesports) ? theSettings.enable_icafesports : false;
	if (!theIsHomeVersion) {
		$('.home-only').hide();
		$('.normal-only').show();
	}
	if (theIsHomeVersion) {
		$('.normal-only').hide();
		$('.home-only').show();

		if (typeof(theCafe) == 'undefined' || typeof(theSettings) == 'undefined') {
			$('#page_login .formDiv').hide();
			$('#page_login .homecafeidDiv').show();
			$('#page_games').removeClass('d-flex').hide();
			$('#page_login').removeClass('d-none').show();
			return;
		}
	}

	try
	{
		run_protect(theSettings.protection_settings ?? null);
		CallFunction("NOOP");
	}
	catch(e)
	{
		// for dev debug in chrome
		CallFunction = function(cmd)
		{
		}

		show_login_page('login');

		thePCStatus = {'member_account': 'test', 'member_group_id': 9,'member_balance_realtime': 888, member_balance_bonus_realtime: 777, member_coin_balance: 666, 'member_group_name': 'testGroup', 'available_offers': [{product_name: 'testOffer', product_seconds: 1000, member_offer_left_seconds: 1000}], 'member_balance_bonus_left_seconds': 1000, 'member_points': 201};
		memberInfo.member_info_name = thePCStatus.member_account.toUpperCase() + " / " + thePCStatus.member_group_name.toUpperCase();

		theHome.show();

		$('.cafe_info_member_logo').attr('src', 'icons/mg-' + (thePCStatus.member_group_id > MEMBER_GROUP_DEFAULT ? thePCStatus.member_group_id.toString() : '0') + '.png');
	
		theAvailableOffers = [];
		var id = 1;
		for (var i=0; i<thePCStatus.available_offers.length; i++)
		{
			var in_using = (thePCStatus.available_offers[i].product_name == thePCStatus.offer_in_using && i == 0);
			theAvailableOffers.push({
				id: id++,
				in_using: in_using,
				time_type: 'offer',
				name: thePCStatus.available_offers[i].product_name.toUpperCase(),
				total_secs: thePCStatus.available_offers[i].product_seconds,
				left_secs: (in_using ? thePCStatus.status_connect_time_left : thePCStatus.available_offers[i].member_offer_left_seconds),
				last_notify_mins: 1000,
				active: ''
			});
		}

		if (thePCStatus.member_balance_bonus_left_seconds > 0)
		{
			var in_using = (thePCStatus.offer_in_using == null || thePCStatus.offer_in_using.length == 0);
			var name = translate_string('BALANCE');
			var left_secs = in_using ? thePCStatus.status_connect_time_left : thePCStatus.member_balance_bonus_left_seconds;

			theAvailableOffers.push({
				id: id++,
				in_using: in_using,
				time_type: 'balance',
				name: name,
				total_secs: thePCStatus.member_balance_bonus_left_seconds,
				left_secs: left_secs,
				last_notify_mins: 1000,
				active: ''
			});
		}

		// add total
		if (theAvailableOffers.length > 0)
		{
			var total_secs = 0;
			var left_secs = 0;
			theAvailableOffers.forEach(function(obj) {
				total_secs += obj.total_secs;
				left_secs += obj.left_secs;
			});

			theAvailableOffers.splice(0, 0, {
				id: id++,
				in_using: false,
				time_type: 'total',
				name: translate_string('TOTAL'),
				total_secs: total_secs,
				left_secs: left_secs,
				last_notify_mins: 1000,
				active: ''
			});
		}

		if (theAvailableOffers.length > 0)
		{
			theAvailableOffers[0].in_using = true;
			theAvailableOffers[0].active = 'active';
		}

		vueAvailableOffers.items = JSON.parse(JSON.stringify(theAvailableOffers));
		
		$('#carousel_main').carousel({ interval: false });

		// show left money and bonus
		$('.member_balance_realtime').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE ? 'd-flex' : 'd-none');
		$('.member_balance_bonus_realtime').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID ? 'd-flex' : 'd-none');
		$('.member_coin_balance').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE && thePCStatus.member_group_id != MEMBER_GROUP_PREPAID ? 'd-flex' : 'd-none');
		$('.postpaid_pc_name').removeClass('d-flex d-none').addClass(thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID || thePCStatus.member_group_id == MEMBER_GROUP_FREE ? 'd-flex' : 'd-none');

		if (theSettings.license_using_billing == 1 && thePCStatus.member_group_id != MEMBER_GROUP_POSTPAID && thePCStatus.member_group_id != MEMBER_GROUP_FREE) {
			var member_balance_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_realtime), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_balance_realtime > 1000000)
				member_balance_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_realtime / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_balance_realtime = member_balance_realtime;

			var member_balance_bonus_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_bonus_realtime), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_balance_bonus_realtime > 1000000)
				member_balance_bonus_realtime = accounting.formatMoney(parseFloat(thePCStatus.member_balance_bonus_realtime / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_balance_bonus_realtime = member_balance_bonus_realtime;

			var member_coin_balance = accounting.formatMoney(parseFloat(thePCStatus.member_coin_balance), '', 2, ' ', '.').replace('.00', '');
			if (thePCStatus.member_coin_balance > 1000000)
				member_coin_balance = accounting.formatMoney(parseFloat(thePCStatus.member_coin_balance / 1000000.0), '', 2, ' ', '.').replace('.00', '') + "M";
			memberInfo.member_coin_balance = member_coin_balance;
		}
		
		vueHome.leaderboardItems = JSON.parse(JSON.stringify(
			{
				"last_month": [{
					"track_member_id": 4342284,
					"track_member_account": "aliitawi",
					"track_game_coins": "5723",
					"track_wins": "57",
					"rank": 1,
					"previous_rank": 1
				}, {
					"track_member_id": 312065975726,
					"track_member_account": "hael",
					"track_game_coins": "4516.6",
					"track_wins": "38",
					"rank": 2,
					"previous_rank": 2
				}, {
					"track_member_id": 4342324,
					"track_member_account": "ramitaiba",
					"track_game_coins": "1118",
					"track_wins": "13",
					"rank": 3,
					"previous_rank": 5
				}, {
					"track_member_id": 312067632456,
					"track_member_account": "nabil558",
					"track_game_coins": "1093",
					"track_wins": "1",
					"rank": 4,
					"previous_rank": 0
				}, {
					"track_member_id": 3408164,
					"track_member_account": "karimkayal",
					"track_game_coins": "821",
					"track_wins": "11",
					"rank": 5,
					"previous_rank": 3
				}, {
					"track_member_id": 3063546152,
					"track_member_account": "hoblos",
					"track_game_coins": "648.5",
					"track_wins": "8",
					"rank": 6,
					"previous_rank": 0
				}],
				"current_month": [{
					"track_member_id": 312065975726,
					"track_member_account": "haelxxxxxxxxxxxxxxxxxxxx",
					"track_game_coins": "530",
					"track_wins": "4",
					"rank": 1,
					"previous_rank": 2
				}, {
					"track_member_id": 312067632966,
					"track_member_account": "ME",
					"track_game_coins": "132.5",
					"track_wins": "1",
					"rank": 2,
					"previous_rank": 0
				}, {
					"track_member_id": 312066792082,
					"track_member_account": "najib1",
					"track_game_coins": "88.5",
					"track_wins": "1",
					"rank": 3,
					"previous_rank": 0
				}, {
					"track_member_id": 312067632968,
					"track_member_account": "os88",
					"track_game_coins": "80.5",
					"track_wins": "1",
					"rank": 4,
					"previous_rank": 0
				}, {
					"track_member_id": 5154524,
					"track_member_account": "rakana",
					"track_game_coins": "54",
					"track_wins": "1",
					"rank": 5,
					"previous_rank": 0
				}, {
					"track_member_id": 312061500211,
					"track_member_account": "fouad1234",
					"track_game_coins": "42.5",
					"track_wins": "0",
					"rank": 6,
					"previous_rank": 0
				}]
			}
		));
		
		// promoted products
		theShop.change_group(-4);
		
		//event-list
		theEvents.events = 
			[{
				"event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
				"event_icafe_id": 18875,
				"event_name": "AAA",
				"event_description": "How to join?\r\nClick the join icon, enter your email address and Telegram username, and then click the Join button. In the pop-up browser, follow the prompts to join our Telegram group (name: iCafeCloud Events). If you have already joined, you can skip this step.\r\n\r\nWhy do I have to join the Telegram group?\r\nYou may encounter the following question: Why don\u2019t I have points when I play the game? How are points calculated? What is the daily ranking change? What's new event? When does it begin? How to collect bonus? Can I organize a competition by myself? You can talk to us directly in the Telegram group.\r\n\r\nWhich games does this Event support?\r\nFortnite\r\nLeague of Legends\r\nDota 2\r\nValorant\r\nAfter you join, you can play any game during the one-month competition period. Each game of yours will be counted as points. The more you play, the higher the points, and there are no restrictions.\r\n\r\nHow to calculate points?\r\nFortnite\u2019s integral calculation formula is:\r\nKills x 3\r\nTop 1 = +9 points\r\n\r\nThe formula for calculating League of Legends points is:\r\nWins x 3\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLOL mode x 1.5\r\nTFT mode x 1.25\r\nKills from 11 to 999 = +2 points\r\nAssists from 11 to 9999 = +2 points\r\n\r\nDota2\u2019s integral calculation formula is:\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLastHits x 0.01\r\nKills from 11 to 999 = +10 points\r\nAssists from 11 to 999 = +10 points\r\n\r\nValorant's integral calculation formula is:\r\nAssists x 0.5\r\nKills x 2\r\nWin = +20 points\r\n\r\nBecause each game has a different difficulty in obtaining points, for the sake of fairness, according to big data analysis, the points of each game should be multiplied by the weight value to calculate the total score, specifically: Fornite weight value is 1, League of Legends is 0.06 , Dota2 is 0.065, Valorant is 0.177.\r\n\r\nHow to win the game?\r\nPlay as many games as possible. We don't have any restrictions. The more you play, the higher the points. In order to increase your participation, we take the top 50 as the winners and all can get bonuses.\r\n\r\nHow to get bonus?\r\nFor convenience, our bonus pool is the data currency DOGE. Please abide by the laws and regulations of your country. If it is not allowed, please do not join our competition. After the competition is over, we will distribute bonuses based on the points of the top 50 players. We will notify the winners one by one in the Telegram group and communicate the payment of funds.\r\n\r\nHave fun and Good luck !!\r\n\r\nJoin our gaming community at telegram\r\nhttps:\/\/www.icafecloud.com\/telegram\/",
				"event_game_code": "dota2",
				"event_game_mode": "",
				"event_start_time_utc": "2022-12-06 16:00:00",
				"event_end_time_utc": "2025-09-08 04:00:00",
				"event_score_type": "all",
				"event_top_winners": 3,
				"event_top_matches": 1000,
				"event_bonus_amount": "200.00",
				"event_bonus_currency": "DOGE",
				"event_ticket_price": "0.00",
				"event_is_global": 0,
				"event_update_time": "2023-05-02 20:30:47",
				"event_start_time_local": "2022-12-07 00:00:00",
				"event_end_time_local": "2025-09-08 12:00:00",
				"event_in_banner": 1,
				"event_play_command": "{steam-path}\\steam.exe -silent -noverifyfiles -applaunch 570",
				"emember_id": "05ba2bf1-765d-11ed-aaf5-f23c93e24cac",
				"emember_event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
				"emember_icafe_id": 18875,
				"emember_member_account": "test",
				"emember_email": "",
				"emember_matches": 0,
				"emember_point_matches": 0,
				"emember_point": 0,
				"emember_wins": 0,
				"emember_kills": 0,
				"emember_assists": 0,
				"emember_deaths": 0,
				"emember_lasthits": 0,
				"emember_game_track_id": 0,
				"emember_ticket_amount": "0.00",
				"emember_bonus": "0.00",
				"emember_bonus_coin_address": "",
				"emember_bonus_pay_status": 0,
				"emember_bonus_trade_id": "",
				"emember_create_time_utc": "2022-12-07 18:29:01",
				"emember_rank_score": 0,
				"emember_status": 1,
				"emember_telegram_username": "",
				"emember_rank": 1,
				"emember_count": 2
			},{
				"event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cad",
				"event_icafe_id": 18875,
				"event_name": "CCC",
				"event_description": "How to join?\r\nClick the join icon, enter your email address and Telegram username, and then click the Join button. In the pop-up browser, follow the prompts to join our Telegram group (name: iCafeCloud Events). If you have already joined, you can skip this step.\r\n\r\nWhy do I have to join the Telegram group?\r\nYou may encounter the following question: Why don\u2019t I have points when I play the game? How are points calculated? What is the daily ranking change? What's new event? When does it begin? How to collect bonus? Can I organize a competition by myself? You can talk to us directly in the Telegram group.\r\n\r\nWhich games does this Event support?\r\nFortnite\r\nLeague of Legends\r\nDota 2\r\nValorant\r\nAfter you join, you can play any game during the one-month competition period. Each game of yours will be counted as points. The more you play, the higher the points, and there are no restrictions.\r\n\r\nHow to calculate points?\r\nFortnite\u2019s integral calculation formula is:\r\nKills x 3\r\nTop 1 = +9 points\r\n\r\nThe formula for calculating League of Legends points is:\r\nWins x 3\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLOL mode x 1.5\r\nTFT mode x 1.25\r\nKills from 11 to 999 = +2 points\r\nAssists from 11 to 9999 = +2 points\r\n\r\nDota2\u2019s integral calculation formula is:\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLastHits x 0.01\r\nKills from 11 to 999 = +10 points\r\nAssists from 11 to 999 = +10 points\r\n\r\nValorant's integral calculation formula is:\r\nAssists x 0.5\r\nKills x 2\r\nWin = +20 points\r\n\r\nBecause each game has a different difficulty in obtaining points, for the sake of fairness, according to big data analysis, the points of each game should be multiplied by the weight value to calculate the total score, specifically: Fornite weight value is 1, League of Legends is 0.06 , Dota2 is 0.065, Valorant is 0.177.\r\n\r\nHow to win the game?\r\nPlay as many games as possible. We don't have any restrictions. The more you play, the higher the points. In order to increase your participation, we take the top 50 as the winners and all can get bonuses.\r\n\r\nHow to get bonus?\r\nFor convenience, our bonus pool is the data currency DOGE. Please abide by the laws and regulations of your country. If it is not allowed, please do not join our competition. After the competition is over, we will distribute bonuses based on the points of the top 50 players. We will notify the winners one by one in the Telegram group and communicate the payment of funds.\r\n\r\nHave fun and Good luck !!\r\n\r\nJoin our gaming community at telegram\r\nhttps:\/\/www.icafecloud.com\/telegram\/",
				"event_game_code": "dota2",
				"event_game_mode": "",
				"event_start_time_utc": "2022-12-06 16:00:00",
				"event_end_time_utc": "2022-12-08 04:00:00",
				
				"event_ticket_price": "0.00",
				"event_is_global": 0,
				"event_update_time": "2023-05-02 20:30:47",
				"event_start_time_local": "2022-12-07 00:00:00",
				"event_end_time_local": "2022-12-08 12:00:00",
				"event_in_banner": 1,
				"event_play_command": "{steam-path}\\steam.exe -silent -noverifyfiles -applaunch 570",
				"emember_id": "05ba2bf1-765d-11ed-aaf5-f23c93e24cad",
				"emember_event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cad",
				"emember_icafe_id": 18875,
				"emember_member_account": "test",
				"emember_email": "",
				"emember_matches": 0,
				"emember_point_matches": 0,
				"emember_point": 0,
				"emember_wins": 0,
				"emember_kills": 0,
				"emember_assists": 0,
				"emember_deaths": 0,
				"emember_lasthits": 0,
				"emember_game_track_id": 0,
				"emember_ticket_amount": "0.00",
				"emember_bonus": "0.00",
				"emember_bonus_coin_address": "",
				"emember_bonus_pay_status": 0,
				"emember_bonus_trade_id": "",
				"emember_create_time_utc": "2022-12-07 18:29:01",
				"emember_rank_score": 0,
				"emember_status": 1,
				"emember_telegram_username": "",
				"emember_rank": 1,
				"emember_count": 2
			}, {
				"event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24caa",
				"event_icafe_id": 18875,
				"event_name": "BBB",
				"event_description": "How to join?\r\nClick the join icon, enter your email address and Telegram username, and then click the Join button. In the pop-up browser, follow the prompts to join our Telegram group (name: iCafeCloud Events). If you have already joined, you can skip this step.\r\n\r\nWhy do I have to join the Telegram group?\r\nYou may encounter the following question: Why don\u2019t I have points when I play the game? How are points calculated? What is the daily ranking change? What's new event? When does it begin? How to collect bonus? Can I organize a competition by myself? You can talk to us directly in the Telegram group.\r\n\r\nWhich games does this Event support?\r\nFortnite\r\nLeague of Legends\r\nDota 2\r\nValorant\r\nAfter you join, you can play any game during the one-month competition period. Each game of yours will be counted as points. The more you play, the higher the points, and there are no restrictions.\r\n\r\nHow to calculate points?\r\nFortnite\u2019s integral calculation formula is:\r\nKills x 3\r\nTop 1 = +9 points\r\n\r\nThe formula for calculating League of Legends points is:\r\nWins x 3\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLOL mode x 1.5\r\nTFT mode x 1.25\r\nKills from 11 to 999 = +2 points\r\nAssists from 11 to 9999 = +2 points\r\n\r\nDota2\u2019s integral calculation formula is:\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLastHits x 0.01\r\nKills from 11 to 999 = +10 points\r\nAssists from 11 to 999 = +10 points\r\n\r\nValorant's integral calculation formula is:\r\nAssists x 0.5\r\nKills x 2\r\nWin = +20 points\r\n\r\nBecause each game has a different difficulty in obtaining points, for the sake of fairness, according to big data analysis, the points of each game should be multiplied by the weight value to calculate the total score, specifically: Fornite weight value is 1, League of Legends is 0.06 , Dota2 is 0.065, Valorant is 0.177.\r\n\r\nHow to win the game?\r\nPlay as many games as possible. We don't have any restrictions. The more you play, the higher the points. In order to increase your participation, we take the top 50 as the winners and all can get bonuses.\r\n\r\nHow to get bonus?\r\nFor convenience, our bonus pool is the data currency DOGE. Please abide by the laws and regulations of your country. If it is not allowed, please do not join our competition. After the competition is over, we will distribute bonuses based on the points of the top 50 players. We will notify the winners one by one in the Telegram group and communicate the payment of funds.\r\n\r\nHave fun and Good luck !!\r\n\r\nJoin our gaming community at telegram\r\nhttps:\/\/www.icafecloud.com\/telegram\/",
				"event_game_code": "dota2",
				"event_game_mode": "",
				"event_start_time_utc": "2022-12-06 16:00:00",
				"event_end_time_utc": "2025-09-08 04:00:00",
				"event_score_type": "all",
				"event_top_winners": 3,
				"event_top_matches": 1000,
				"event_bonus_amount": "200.00",
				"event_bonus_currency": "DOGE",
				"event_ticket_price": "0.00",
				"event_is_global": 0,
				"event_update_time": "2023-05-02 20:30:47",
				"event_start_time_local": "2022-12-07 00:00:00",
				"event_end_time_local": "2025-09-08 12:00:00",
				"event_in_banner": 1,
				"event_play_command": "{steam-path}\\steam.exe -silent -noverifyfiles -applaunch 570",
				"event_status": 'active'
			}];
		theEvents.build_event_list_html();
		//event-detail
		var eventData = 
			{
				"event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
				"event_icafe_id": 18875,
				"event_name": "AAA",
				"event_description": "How to join?\r\nClick the join icon, enter your email address and Telegram username, and then click the Join button. In the pop-up browser, follow the prompts to join our Telegram group (name: iCafeCloud Events). If you have already joined, you can skip this step.\r\n\r\nWhy do I have to join the Telegram group?\r\nYou may encounter the following question: Why don\u2019t I have points when I play the game? How are points calculated? What is the daily ranking change? What's new event? When does it begin? How to collect bonus? Can I organize a competition by myself? You can talk to us directly in the Telegram group.\r\n\r\nWhich games does this Event support?\r\nFortnite\r\nLeague of Legends\r\nDota 2\r\nValorant\r\nAfter you join, you can play any game during the one-month competition period. Each game of yours will be counted as points. The more you play, the higher the points, and there are no restrictions.\r\n\r\nHow to calculate points?\r\nFortnite\u2019s integral calculation formula is:\r\nKills x 3\r\nTop 1 = +9 points\r\n\r\nThe formula for calculating League of Legends points is:\r\nWins x 3\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLOL mode x 1.5\r\nTFT mode x 1.25\r\nKills from 11 to 999 = +2 points\r\nAssists from 11 to 9999 = +2 points\r\n\r\nDota2\u2019s integral calculation formula is:\r\nKills x 2\r\nAssists x 1.5\r\nDeaths x -0.5\r\nLastHits x 0.01\r\nKills from 11 to 999 = +10 points\r\nAssists from 11 to 999 = +10 points\r\n\r\nValorant's integral calculation formula is:\r\nAssists x 0.5\r\nKills x 2\r\nWin = +20 points\r\n\r\nBecause each game has a different difficulty in obtaining points, for the sake of fairness, according to big data analysis, the points of each game should be multiplied by the weight value to calculate the total score, specifically: Fornite weight value is 1, League of Legends is 0.06 , Dota2 is 0.065, Valorant is 0.177.\r\n\r\nHow to win the game?\r\nPlay as many games as possible. We don't have any restrictions. The more you play, the higher the points. In order to increase your participation, we take the top 50 as the winners and all can get bonuses.\r\n\r\nHow to get bonus?\r\nFor convenience, our bonus pool is the data currency DOGE. Please abide by the laws and regulations of your country. If it is not allowed, please do not join our competition. After the competition is over, we will distribute bonuses based on the points of the top 50 players. We will notify the winners one by one in the Telegram group and communicate the payment of funds.\r\n\r\nHave fun and Good luck !!\r\n\r\nJoin our gaming community at telegram\r\nhttps:\/\/www.icafecloud.com\/telegram\/",
				"event_game_code": "dota2",
				"event_game_mode": "",
				"event_start_time_utc": "2022-12-06 16:00:00",
				"event_end_time_utc": "2025-09-08 04:00:00",
				"event_score_type": "all",
				"event_top_winners": 3,
				"event_top_matches": 1000,
				"event_bonus_amount": "200.00",
				"event_bonus_currency": "DOGE",
				"event_ticket_price": "0.00",
				"event_is_global": 0,
				"event_update_time": "2023-05-02 20:30:47",
				"event_start_time_local": "2022-12-07 00:00:00",
				"event_end_time_local": "2025-09-08 12:00:00",
				"event_in_banner": 1,
				"event_play_command": "{steam-path}\\steam.exe -silent -noverifyfiles -applaunch 570",
				"emember_id": "05ba2bf1-765d-11ed-aaf5-f23c93e24cac",
				"emember_event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
				"emember_icafe_id": 18875,
				"emember_member_account": "test",
				"emember_email": "",
				"emember_matches": 0,
				"emember_point_matches": 0,
				"emember_point": 0,
				"emember_wins": 0,
				"emember_kills": 0,
				"emember_assists": 0,
				"emember_deaths": 0,
				"emember_lasthits": 0,
				"emember_game_track_id": 0,
				"emember_ticket_amount": "0.00",
				"emember_bonus": "0.00",
				"emember_bonus_coin_address": "",
				"emember_bonus_pay_status": 0,
				"emember_bonus_trade_id": "",
				"emember_create_time_utc": "2022-12-07 18:29:01",
				"emember_rank_score": 0,
				"emember_status": 1,
				"emember_telegram_username": "",
				"emember_rank": 1,
				"emember_count": 2,
				"members": [{
					"emember_id": "18c1ceba-d6e8-11ed-b1de-f23c93e24cac",
					"emember_event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
					"emember_icafe_id": 18875,
					"emember_member_account": "bin",
					"emember_email": "",
					"emember_matches": 0,
					"emember_point_matches": 0,
					"emember_point": 0,
					"emember_wins": 0,
					"emember_kills": 0,
					"emember_assists": 0,
					"emember_deaths": 0,
					"emember_lasthits": 0,
					"emember_game_track_id": 0,
					"emember_ticket_amount": "0.00",
					"emember_bonus": "0.00",
					"emember_bonus_coin_address": "",
					"emember_bonus_pay_status": 0,
					"emember_bonus_trade_id": "",
					"emember_create_time_utc": "2023-04-09 15:06:25",
					"emember_rank_score": 0,
					"emember_status": 1,
					"emember_telegram_username": "",
					"emember_rank": 1
				}, {
					"emember_id": "05ba2bf1-765d-11ed-aaf5-f23c93e24cac",
					"emember_event_id": "d94eddf1-765c-11ed-aaf5-f23c93e24cac",
					"emember_icafe_id": 18875,
					"emember_member_account": "test",
					"emember_email": "",
					"emember_matches": 0,
					"emember_point_matches": 0,
					"emember_point": 0,
					"emember_wins": 0,
					"emember_kills": 0,
					"emember_assists": 0,
					"emember_deaths": 0,
					"emember_lasthits": 0,
					"emember_game_track_id": 0,
					"emember_ticket_amount": "0.00",
					"emember_bonus": "0.00",
					"emember_bonus_coin_address": "",
					"emember_bonus_pay_status": 0,
					"emember_bonus_trade_id": "",
					"emember_create_time_utc": "2022-12-07 18:29:01",
					"emember_rank_score": 0,
					"emember_status": 1,
					"emember_telegram_username": "",
					"emember_rank": 2
				}]
			};
		for (var i=0; i<theEvents.events.length; i++) {
			if (theEvents.events[i].event_id == eventData.event_id) {
				theEvents.events[i] = eventData;

				theEvents.events[i].event_status = 'active';
				if (moment(theEvents.events[i].event_end_time_local).isBefore())
					theEvents.events[i].event_status = 'past';
				if (moment(theEvents.events[i].event_start_time_local).isAfter())
					theEvents.events[i].event_status = 'upcoming';

				theEvents.gamecode2names.forEach(function(game) {
					if (theEvents.events[i].event_game_code == game.code) {
						theEvents.events[i].game_name = game.name;
					}
				});

				// If current member record need push to members end
				if (theEvents.events[i].members.length > 0 && theEvents.events[i].emember_id && theEvents.events[i].emember_rank > theEvents.events[i].members[theEvents.events[i].members.length-1].emember_rank) {
					theEvents.events[i].members.push({
						emember_id: theEvents.events[i].emember_id,
						emember_member_account: theEvents.events[i].emember_member_account,
						emember_rank: theEvents.events[i].emember_rank,
						emember_matches: theEvents.events[i].emember_matches,
						emember_point_matches: theEvents.events[i].emember_point_matches,
						emember_bonus: theEvents.events[i].emember_bonus,
						emember_point: theEvents.events[i].emember_point,
						emember_wins: theEvents.events[i].emember_wins,
						emember_kills: theEvents.events[i].emember_kills,
						emember_assists: theEvents.events[i].emember_assists,
						emember_deaths: theEvents.events[i].emember_deaths,
						emember_lasthits: theEvents.events[i].emember_lasthits,
						license_country: theEvents.events[i].license_country,
						license_icafename: theEvents.events[i].license_icafename
					});
				}
				break;
			}
		}

		theEvents.build_event_list_html();
		theEvents.build_event_detail_html(eventData.event_id);
		
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
		return;
	}

	show_login_page('login');

	if (theIsHomeVersion) {
		unlock_all();
		CallFunction("SETWINDOWSIZE -2*-2");
		theLastWindowSize = "-2*-2";
	}

	CallFunction("WSSSTART");
}

$(document).ready(main);

$(window).bind("load resize", function() {
	setBodyStyle();

	/*
	var topOffset = 190;
	var win_height = ((this.window.innerHeight > 0) ? this.window.innerHeight : this.screen.height) - 1;
	var height = win_height - topOffset;
	if (height < 1) height = 1;
	if (height > topOffset) {
		$("#games #game_items").css("height", (height) + "px");
		$("#games #game_items").css("min-height", (height) + "px");
		//$("#games #product-list").css("height", (height) + "px");
		//$("#games #product-list").css("min-height", (height) + "px");
		$("#games #product_groups").css("height", (height) + "px");
		$("#games #product_groups").css("min-height", (height) + "px");
	}
	
	if(window.innerWidth > screen.width){
		$("#page_login").css("width", "50%");
		$("#page_lock section").css("width", "50%");
	}
	if(window.innerHeight > screen.height){
		$("#page_login").css("height", "50%");
		$("#page_lock section").css("height", "50%");
	}
	*/
	

	//This part is not required as bootstrap has modal-dialog-centered to make the modal appear in center of the screen.
	/* 
	win_height = parseInt(win_height * 0.9, 10);
	$('.myModalConfirmCheckout .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalConfirmCheckout .modal-content').css('margin-top', parseInt((win_height - 233) / 2, 10) + 'px');

	$('.myModalMessage .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalMessage .modal-content').css('margin-top', parseInt((win_height - 233) / 2, 10) + 'px');

	$('.myModalFeedback .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalFeedback .modal-content').css('margin-top', parseInt((win_height - 389) / 2, 10) + 'px');

	$('.myModalLock .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalLock .modal-content').css('margin-top', parseInt((win_height - 318) / 2, 10) + 'px');

	$('.myModalChangePassword .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalChangePassword .modal-content').css('margin-top', parseInt((win_height - 622) / 2, 10) + 'px');

	$('.myModalRunGame .modal-dialog').css('max-height', win_height  + 'px');
	$('.myModalRunGame .modal-content').css('margin-top', parseInt((win_height - 622) / 2, 10) + 'px');
	*/
	if (is_logined() && $('#games .games-container').is(":visible"))
		theGameList.load_games_by_class(theGameList.filter_params.type, theGameList.filter_params.class, theGameList.filter_params.search);
});


$(document).keydown(function (event)
{
	theMonitorTurnOffStartTime = new Date();

	if (!is_logined()) {
		if (event.keyCode == 27)
			show_login_page('admin_exit');
		return;
	}

	if (is_locked())
		return;

	// logined and not locking
	// X = 88, B = 66, F = 70, F1 = 112
	if (event.ctrlKey && event.keyCode == 112)
		send_assist();

	if (event.ctrlKey && event.keyCode == 70)
		$('input#search-bar').focus();

	if (event.ctrlKey && event.keyCode == 88)
		checkout_click();

	if (event.ctrlKey && event.keyCode == 66)
		theShop.show();

	if (theSettings == null || typeof(theSettings.license_show_client_mode) == 'undefined' || theSettings.license_show_client_mode != 'full screen') {
		if (event.ctrlKey && event.keyCode == 'M'.charCodeAt(0))
			CallFunction('HIDEWINDOW');
	}
});

$(document).mousedown(function(event) {
	if (!is_logined())
		theMonitorTurnOffStartTime = new Date();
	return true;
});

function setBodyStyle()
{
	return;
	let standardRatio = 1920.0 / 1080;
	let pageRatio = window.innerWidth / window.innerHeight;

	let containerWidth;
	let containerHeight;
	let zoom = 1;
	let margin;
	if(standardRatio > pageRatio) {
		containerWidth = window.innerWidth;
		containerHeight = 1080 * window.innerWidth / 1920;
		zoom = containerHeight / 1080;
		margin = (window.innerHeight - containerHeight) / 2 + "px 0";
	} else {
		containerWidth = 1920 * window.innerHeight / 1080;
		containerHeight = window.innerHeight
		zoom = containerWidth / 1920;
		margin = "0 0 0 " + (window.innerWidth - containerWidth) / 2 + "px";
	}

	let bodyStyle = {
		width: "1920px",
		height: "1080px",
		'background-color': "#000000",
		//transform: "scale("+zoom+")",
		//'transform-origin': "top left",
		margin: margin,
		//'background-image': "none"
	}

	vueGlobal.bodyStyle = JSON.parse(JSON.stringify(bodyStyle));
}

function countdown()
{
	if (thePCStatus.status_connect_time_left < 0)
	{
		// The end of the countdown does not mean the customer time is all used up, because the customer may have offers and balance.
		// send auto_checkout package to wss server, the wss server will send client_status package to me after switch to another offer or balance.
		var cmd = {action: 'auto_checkout', version: 2,	type: 'request', from: 'client', target: 'wss-server',	data: {}};
		CallFunction('WSSSEND ' + JSON.stringify(cmd));

		clearInterval(theCountDownIntervalId);
		theCountDownIntervalId = null;
		return;
	}
	
	if (thePCStatus.member_group_id == MEMBER_GROUP_POSTPAID || thePCStatus.member_group_id == MEMBER_GROUP_FREE) {
		memberInfo.postpaid_pc_name = thePCStatus.pc_name;
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});

		thePCStatus.status_connect_time_duration += 1;  // if postpaid, show time used
		if(theAvailableOffers.length > 0)
			theAvailableOffers[0].left_secs = thePCStatus.status_connect_time_duration;
	}

	for (var i=0; i<theAvailableOffers.length; i++) {
		var percent = 0;
		if (theAvailableOffers[i].total_secs > 0)
			percent = Math.min(parseInt((theAvailableOffers[i].left_secs / theAvailableOffers[i].total_secs) * 100.0), 100);

		$('#available-' + theAvailableOffers[i].id + ' .progress-bar').css('width', percent + '%');
		$('#available-' + theAvailableOffers[i].id + ' .remaining').html(format_time(theAvailableOffers[i].left_secs));
	}

	if(((typeof(theSettings.alert_for_last_offer) == 'undefined' || theSettings.alert_for_last_offer == 1) && theAvailableOffers.length == 3) || theAvailableOffers.length == 2) // total, last offer, balance
	{
		var hour = parseInt(theAvailableOffers[1].left_secs / 3600);
		var min = parseInt((theAvailableOffers[1].left_secs % 3600) / 60);
		for (var m=1; m<=5; m++)
		{
			if(hour > 0)
				break;
			if(theAvailableOffers[1].last_notify_mins <= m)
				break;
			if (min < m) 
			{
				if(theAvailableOffers.length == 3)
					toast(translate_string('{0} offer will be expired in {1} minutes, auto switch to balance mode').replace('{0}', theAvailableOffers[1].name).replace('{1}', m), 'warning');
				else
					toast(translate_string("Your remaining time is less than {0} minutes").replace('{0}', m), 'warning');
				CallFunction("PLAYSOUND customized/" + m + "min_left.wav "  + m + "min_left.wav");
				theAvailableOffers[1].last_notify_mins = m;
				break;
			}
		}
	}

	thePCStatus.status_connect_time_left -= 1;

	for (i=0; i<theAvailableOffers.length; i++) {
		if (theAvailableOffers[i].time_type === 'total' || theAvailableOffers[i].in_using) {
			theAvailableOffers[i].left_secs -= 1;
		}
	}
}

function query_rungame_ids()
{
	CallFunction("RUNGAME_QUERY_IDS");
}

// sub_div => login, member_register, admin_exit
function show_login_page(sub_div)
{
	CallFunction("LOCK 65535");

	CallFunction("SETWINDOWSIZE -1*-1");
	CallFunction("SETWINDOWTOPMOST 1");
	theLastWindowSize = "-1*-1";

	var MONTHs = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"];
	var d = new Date();
	var current_month = d.getMonth();
	var current_year = d.getFullYear();

	var last_month = current_month-1;
	var last_year = current_year;
	if (last_month < 0) {
		last_month = 11;
		last_year -= 1;
	}

	$('body').css({'background-image': "url('posters/cafe_info_cafe_login.jpg'), url('images/games.jpg')"});

	$('#loginForm input[name=username]').prop('disabled', !theWssLogined);
	$('#loginForm input[name=password]').prop('disabled', !theWssLogined);
	$('#loginForm input[name=username]').val('');
	$('#loginForm input[name=password]').val('');
	var opacity = 1.0;
	if (!theWssLogined)
		opacity = 0.5;
	$('#loginForm button').css({opacity: opacity});

	if (theIsHomeVersion)
		$('#loginForm input[name=username]').val(thePCInfo.pc_name);
	else
		$('#page_login .pc_name').html(thePCInfo.pc_name);

	$('.myModalBuy').modal('hide');
	$('.myModalLockPassword').modal('hide');
	$('.myModalChangePassword').modal('hide');
	$('.myModalConfirmCheckout').modal('hide');
	$('.myModalFeedback').modal('hide');
	$('.myModalRunGame').modal('hide');
	$('.myModalConvertMember').modal('hide');
	$('#page_games').removeClass('d-flex').hide();
	$('#page_login').removeClass('d-none').show();

	$('#page_login .loginDiv').hide();
	$('#page_login .registerDiv').hide();
	$('#page_login .adminexitDiv').hide();
	$('#page_login .homecafeidDiv').hide();

	if (sub_div == 'login') {
		$('#page_login .loginDiv').show();
		document.getElementById('username').focus();
	}

	if (sub_div == 'member_register')
		$('#page_login .registerDiv').show();

	if (sub_div == 'admin_exit') {
		$('#adminexitForm input[name=password]').val('');
		$('#page_login .adminexitDiv').show();
	}

	set_monitor_turn_off_timeout(thePCInfo.pc_turn_off_monitor_seconds);

}

function Home()
{
	this.show = function() {

		vueGlobal.pageType = "Home";
		vueGlobal.showBottom = true;
		
		setBodyStyle();
		$('body').css({'background-image': "url('posters/cafe_info_cafe_background.jpg'), url('images/games.jpg')"});

		$('#page_login').addClass('d-none').hide();
		$('#page_games').addClass('d-flex').show();

		// Top 5 Games
		let topFiveGames = theGames.sort(theGameList.local_hot_compare).slice(0, 5);
		vueGames.topFiveItems = JSON.parse(JSON.stringify(topFiveGames));

		// Promoted product
		theShop.change_group(-4);
		setDropdownMenu();

		if (is_member_logined())
			vueGlobal.menuButton.changepassword = true;

		// 用户积分
		if((thePCStatus.member_points ?? null) && (theSettings.point_enable ?? 0)) {
			theMemberGroup = theMemberGroup.filter(obj => obj.member_group_id > 0 && obj.member_group_point_min !== undefined)
			.sort((a, b) => parseFloat(a.member_group_point_min) - parseFloat(b.member_group_point_min));

			var memberGroup = [];
			var groupIndex = 1;
			var memberCurrentGroup = 0;
			var memberCurrentGroupPoint = 0;
			theMemberGroup.forEach(function(group) {

				let point_min = parseFloat(group.member_group_point_min);

				if(thePCStatus.member_group_id == group.member_group_id) {
					memberCurrentGroup = groupIndex;
					memberCurrentGroupPoint = (groupIndex == theMemberGroup.length ? point_min : theMemberGroup[groupIndex].member_group_point_min);
				}

				memberGroup.push(
					{
						mebmer_group_index: groupIndex,
						member_group_id: group.member_group_id,
						member_group_name: group.member_group_name,
						member_group_point_min: point_min,
					}
				);

				groupIndex++;
			});
			
			if(memberGroup.length > 0)
			{
				var lastGroupIndex = memberGroup[memberGroup.length - 1].mebmer_group_index;
				var showMemberGroup = [];
				if(memberCurrentGroup == 1 || memberCurrentGroup == 0) {
					showMemberGroup = memberGroup.slice(0, 3);
				} else if(lastGroupIndex == memberCurrentGroup) {
					let startIndex = memberGroup.length > 3 ? memberGroup.length - 3 : 0;
					showMemberGroup = memberGroup.slice(startIndex, memberGroup.length);
				} else {
					showMemberGroup = memberGroup.slice(memberCurrentGroup - 2, memberCurrentGroup + 1);
				}

				if(memberCurrentGroup == 0 && showMemberGroup.length > 0) {
					memberCurrentGroupPoint = showMemberGroup[0].member_group_point_min;
				}

				vueHome.memberCurrentGroup = memberCurrentGroup; 
				vueHome.memberGroup = JSON.parse(JSON.stringify(showMemberGroup));
				vueHome.memberPointValue = thePCStatus.member_points + '/' + memberCurrentGroupPoint;
			}
		}

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
			//that.load_games_by_class('class', 'Favorite', '');
		});
		
		if (typeof(theCafeNews) != 'undefined' && theCafeNews != null && theCafeNews.length > 0) {
			//$('#news_carousel_main .carousel-inner').html(tmpl('tmpl-news', { items: theCafeNews } ));
			//translate_obj($('#news_carousel_main .carousel-inner'));
			for(var i = 0; i < theCafeNews.length; i ++)
			{
				theCafeNews[i].active = '';
			}
			if(theCafeNews.length > 0)
				theCafeNews[0].active = 'active';
			vueCafeNews.items = JSON.parse(JSON.stringify(theCafeNews)).map((item) => {
				item.news_show_qr = typeof(item.news_show_qr) == 'undefined' ? true : item.news_show_qr;
				item.news_video = typeof(item.news_video) == 'undefined' ? '' : item.news_video;
				item.isYoutube = false;
				item.news_duration = typeof(item.news_duration) == 'undefined' ? 5000 : item.news_duration;
				item.news_type = typeof(item.news_type) == 'undefined' ? 'picture' : item.news_type;
				if (item.news_video.match(/youtube/) !== null){
					var videoSplit = item.news_video.split("?v=");
					var videoId = videoSplit ? videoSplit[1] : "";
					if(videoId.length > 0)
					{
						item.isYoutube = true;
						item.news_video = "https://www.youtube.com/embed/" + videoId + "?mute=1&modestbranding=1&autohide=1&showinfo=0&controls=0&autoplay=1&loop=1&playlist=" + videoId + "&version=3";
					}
				}
				
				if(item.news_type === 'picture') {
					item.news_video = ''
				}

				return item;
			});
			
			PetiteVue.nextTick(() => {
				var start = $('#home_carousel_news .carousel-inner').find('.active').attr('data-bs-interval');
				var t = setTimeout("$('#home_carousel_news').carousel({interval: 1000});", start-1000);
				$('#home_carousel_news').on('slid.bs.carousel', function () {
					clearTimeout(t); 
					var duration = $('#home_carousel_news .carousel-inner').find('.active').attr('data-bs-interval');
					 $('#home_carousel_news').carousel('pause');
					 t = setTimeout("$('#home_carousel_news').carousel({interval: 1000});", duration-1000);
				})

				$('#home_carousel_news .carousel-indicators').on('click', function(){
					clearTimeout(t); 
				});

				$('#home_carousel_news .carousel-indicators').on('click', function(){
					clearTimeout(t); 
				});
				ui_init();
				$('[data-toggle="tooltip"]').tooltip();
			});

			//$('#home_carousel_news').carousel({ interval: 1000 });
		}
	
	}
}


function GameList()
{
	this.filter_params = { type: 'home', class: '', search: '' };
	this.member_recent_played = [];
	this.local_hot_sorted_games = [];

	// 进入GAMES页后，所有的处理要重新处理，可以重进入（例如：已经是GAMES页，再进入时，LEFT_TIME要重启一下
	// 置thePCStatus时，就要重启left_time.
	this.show = function() {
		var that = this;

		that.local_hot_sorted_games = theGames.sort(that.local_hot_compare);
		for (var i=0; i<that.local_hot_sorted_games.length; i++) {
			that.local_hot_sorted_games[i].local_hot_rank = i+1;
		}
		//$('#top-buttons .dropdown-menu').html(tmpl('tmpl-more-games-classes', { items: theClasses == null ? [] : theClasses.sort(that.class_compare) }));
		//translate_obj($('#top-buttons'));

		theClasses == null ? [] : theClasses.sort(that.class_compare);
		theClasses = theClasses.filter((item) => {
			item.game_count = 0;
			for (var i=0; i<theGames.length; i++) {
				if(theGames[i].pkg_idc_class == item.class_name)
					item.game_count ++;
			}
			if(item.game_count == 0)
				return false;
			return true;
		});

		theClasses.unshift({class_name: 'All Games'});

		let gameClass = [
			{class_name: 'More', icon: 'fa-bars', subClasses: []},
			{class_name: 'Favorite', icon: 'fa-star'},
			{class_name: 'Free to play', icon: 'fa-bookmark'},
		];

		gameClass[0]['subClasses'] = theClasses;
		vueClasses.items = JSON.parse(JSON.stringify(gameClass));
		
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
			that.load_games_by_class('class', 'All Games', '');
		});

		$('input#search-bar').keyup(function(e){
			var new_search = $(this).val();
			if (that.filter_params.search.toLowerCase() == new_search)
				return;

			that.load_games_by_class('class', 'All Games', $(this).val());
		});
	
		setDropdownMenu();

		// load recent played from client_status package
		if (typeof(thePCStatus.member_recent_played) != 'undefined' && thePCStatus.member_recent_played != null) {
			that.member_recent_played = JSON.parse(thePCStatus.member_recent_played);
		}
	}

	this.class_compare = function(a, b) {
		var ret = 0;
		if (a.class_name.toLowerCase().indexOf('steam') >= 0)
			return -1;
		if (b.class_name.toLowerCase().indexOf('steam') >= 0)
			return 1;

		if (a.class_name.toLowerCase() < b.class_name.toLowerCase())
			ret = -1;
		if (a.class_name.toLowerCase() > b.class_name.toLowerCase())
			ret = 1;

		return ret;
	};

	this.local_hot_compare = function(a, b) {
		var a_is_favorite = a.pkg_favorite;
		var b_is_favorite = b.pkg_favorite;

		var a_value = a.pkg_local_hot || 0;
		var b_value = b.pkg_local_hot || 0;

		if (a_is_favorite && !b_is_favorite)
			return -1;

		if (!a_is_favorite && b_is_favorite)
			return 1;

		var ret = 0;
		if (a_value < b_value)
			ret = -1;
		if (a_value > b_value)
			ret = 1;

		return 0 - ret;
	}

	this.is_recent_played = function(pkg_id) {
		var exists = false;
		this.member_recent_played.forEach(function(game) {
			if (game.pkg_id === parseInt(pkg_id))
				exists = true;
		})
		return exists;
	}

	this.load_games_by_class = function(type, class_name, search) {
		if(class_name == 'Favorite')
			type = 'home';
		if(class_name == 'All Games')
			type = 'all';
		if(class_name == 'Free to play')
			type = 'license';

		acitve_class = class_name;
		class_name = decodeURIComponent(class_name);
		acitve_class = decodeURIComponent(acitve_class);
		$('#more-games').html(type != 'class' ? translate_string('More games') : class_name);
		var that = this;

		that.filter_params = { type: type, class: class_name, search: search };
		$('input#search-bar').val(search);

		// Home, We always show the 5 games on top that member played, then show the favorite games, then order by local hot.
		// All games, it will show favorite games first, then order by local hot.
		// Licensed Games, it will show licensed games, favorite first then local hot.
		// More Games, will show menu of categories, favorite first, then local hot.
		var limit_count = Math.MAX_VALUE;

		{
			var games_width = parseInt($('#games').css('width').replace('px', ''), 10) || 0;
			games_width -= 0;
			var games_height = parseInt($("#games").css("height").replace('px', ''), 10) || 0;
			games_height -= 20;

			var item_width = 168+15;
			var item_height = 264+15;

			if (item_width <= 0)
				return;

			var cols = Math.max(Math.floor(games_width / item_width), 2);
			var rows = Math.max(Math.floor(games_height / item_height), 2);
			if (type === 'home')
				limit_count = cols*rows;

			var width = cols * item_width;
			//$('#games .games-container').css("width", width+ "px");
			var padding = parseInt((games_width - width) / 2);
			//$('#top-buttons').css("padding-left", padding + "px");
			//$('#top-buttons').css("padding-right", padding + "px");
		}

		var sorted_games = that.local_hot_sorted_games.sort(that.local_hot_compare);
		var show_games = [];
		sorted_games.forEach(function(game) {
			if (type === 'home' && that.is_recent_played(game.pkg_id))
				return;

			if (type === 'home' && game.pkg_idc_class.toLowerCase() === 'internet tools')
				return;

			if (game.pkg_name.toLowerCase() === 'icafemenu' || game.pkg_name.toLowerCase() === 'overwolf')
				return;

			if (type === 'license' && !game.pkg_has_license)
				return;

			if (type === 'class' && class_name.length > 0 && game.pkg_idc_class != class_name)
				return;

			if (search.length > 0 && game.pkg_name.toLowerCase().indexOf(search.toLowerCase()) < 0)
				return;

			// pc groups
			var pkg_pc_group_ids = typeof(game.pkg_pc_group_ids) != 'undefined' ? game.pkg_pc_group_ids : [];
			if (pkg_pc_group_ids.length > 0 && pkg_pc_group_ids.indexOf(thePCStatus.pc_group_id) < 0)
				return;

			if (is_member_logined() && game.pkg_rating > 0 && thePCStatus.member_birthday != null && thePCStatus.member_birthday != '0000-00-00') {

				var cols = thePCStatus.member_birthday.split('-');
				if (cols.length === 3) {
					var year = cols[0];
					var month = cols[1];
					var day = cols[2];

					var ts = new Date() - new Date(year, month, day);
					var years = parseInt(ts / (3600 * 24 * 1000) / 365);

					if (years < game.pkg_rating)
						return;
				}

			}

			limit_count = limit_count - 1;
			if (limit_count < 0)
				return;

			if (type === 'home' && limit_count <= theGameList.member_recent_played.length)
				return;

			show_games.push(game);
		});

		if (type === 'home') {
			for (var i=theGameList.member_recent_played.length-1; i>=0; i--) {
				that.local_hot_sorted_games.forEach(function(game) {
					if (theGameList.member_recent_played[i].pkg_id == game.pkg_id)
					{
						var pkg_pc_group_ids = typeof(game.pkg_pc_group_ids) != 'undefined' ? game.pkg_pc_group_ids : [];
						if (pkg_pc_group_ids.length > 0 && pkg_pc_group_ids.indexOf(thePCStatus.pc_group_id) < 0)
							return;
						show_games.unshift(game);
					}
				})
			}
		}
		// $('#games .games-container').html(tmpl('tmpl-games', { items: show_games, type: type }));
		vueGames.items = JSON.parse(JSON.stringify(show_games));
		vueGames.type = type;
		vueGames.active_class = acitve_class;
		vueGames.status_pc_token = thePCStatus.status_pc_token;

		vueGlobal.pageType = "Games";
		vueGlobal.showBottom = true;

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	}

	this.play_game = function(pkg_id, status_pc_token, use_icafecloud_license, license_account) {
		// if use license pool, cover show/hide control by pool, else show cover 3 seconds, prevent users click repeatedly

		CallFunction("RUNGAME " + pkg_id + " " + status_pc_token + " 0 " + use_icafecloud_license + " " + license_account);

		var params = 'type=update-hot&id=' + pkg_id + '&token=' + thePCStatus.status_pc_token;
		CallFunction('API ' + params);
		
		var that = this;

		for (var i=0; i<that.member_recent_played.length; i++) {
			if (that.member_recent_played[i].pkg_id === parseInt(pkg_id)) {
				that.member_recent_played.splice(i, 1);
				break;
			}
		}

		that.member_recent_played.unshift({ pkg_id: parseInt(pkg_id) });
		if (that.member_recent_played.length > 5)
			that.member_recent_played.splice(5,that.member_recent_played.length - 5);
	}
	
	var menu_target_id = null;

	this.request_game_licenses = function(pkg_id, target_id) {
		$.contextMenu('destroy', '#btn-play-with-license-' + pkg_id);
		$.contextMenu('destroy', '#btn-home-play-with-license-' + pkg_id);
		this.menu_target_id = target_id;
		var cmd = {
			action: 'game_licenses',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'wss-server',
			data: {
				pkg_id: pkg_id
			}
		};
		CallFunction('WSSSEND ' + JSON.stringify(cmd));
	}

	this.game_licenses_sort = function(a, b) {
		var a_value = (a.license_status.toUpperCase() == 'FREE' ? 1 : 0);
		var b_value = (b.license_status.toUpperCase() == 'FREE' ? 1 : 0);

		return b_value - a_value;
	}

	this.process_wss_package = function(packet){
		if (packet.action != 'game_licenses')
			return false;
		
		var that = this;
		
		$.contextMenu({
			selector: '#' + that.menu_target_id,
			className: 'play-with-license-title',
			trigger: 'none',
			build: function($trigger, e) {
				e.preventDefault();

				var items = {};
				if (packet.data.licenses.length == 0)
					items['no_free_account'] = { name: translate_string('No free account'), disabled: true };

				if (packet.data.licenses.length > 0) {
					var show_licenses = packet.data.licenses.sort(that.game_licenses_sort);
					show_licenses.forEach(function (license) {
						items[license.license_account] = {
							name: license.license_account,
							disabled: (license.license_status.toUpperCase() != 'FREE'),
							icon: (license.license_status.toUpperCase() != 'FREE' ? 'fal fa-lock' : '')
						};
					});
				}

				return {
					callback: function(key, options) {
						theGameList.play_game(packet.data.pkg_id, thePCStatus.status_pc_token, 1, key);
					},
					items: items
				};
			}
		});

		$('#' + that.menu_target_id).trigger('contextmenu');
		return true;
	}
}

function Shop()
{
	this.order_items = [];
	this.gift_order_items = [];
	this.filtered_items = [];
	this.loaded = false;
	this.current_group_id = -3;
	this.enable_cash = 1;
	this.enable_credit_card = 1;
	this.enable_balance = 1;
	this.search = '';
	var that = this;

	this.show = function() {
		this.order_items = [];

		if (!this.loaded) {
			this.loaded = true;
			theProductGroupList.push({
				product_group_desc: "",
				product_group_has_icon: false,
				product_group_id: -2,
				product_group_name: translate_string("Gifts")
			});

			for (var i=0; i<theProductGroupList.length; i++)
			{
				if (theProductGroupList[i].product_group_id == -2) {
					var total = 0;
					theProductList.forEach(function(obj) {
						if (obj.product_coin_price > 0)
							total += 1;
					});
					theProductGroupList[i].product_count = total;
					continue;
				}

				var total = 0;
				theProductList.forEach(function(obj) {
					if (obj.product_group_id == theProductGroupList[i].product_group_id)
						total += 1;
				});
				theProductGroupList[i].product_count = total;
			}
		}

		//$('#product-group-list ul').html(tmpl('tmpl-product-group', { items: theProductGroupList }));
		//translate_obj($('#product-group-list ul'));
		var items = [];
		let dropdownProductGroupList = [];
		for (var i=0; i<theProductGroupList.length; i++)
		{
			if (theProductGroupList[i].product_count <= 0) continue;

			if (theProductGroupList[i].product_group_id > 0) {
				dropdownProductGroupList.push(theProductGroupList[i]);
			} else {
				items.push(theProductGroupList[i]);
			}
		}

		dropdownProductGroupList.unshift({
			product_group_id: -3,
			product_group_name: translate_string("All"),
		})

		vueProductGroupList.items = JSON.parse(JSON.stringify(items));
		vueProductGroupList.dropdownProductGroupList = JSON.parse(JSON.stringify(dropdownProductGroupList));
		
		this.change_group(-3); // all

		$('#cart_date').html(this.format_date());
		// $('#cart').html(tmpl('tmpl-new-order-items', { items: [] }));
		vueOrderItems.total_cost = 0;
		vueOrderItems.total_tax = 0;
		vueOrderItems.total_amount = 0;
		vueOrderItems.total_discount = 0;
		vueOrderItems.member_group_id = thePCStatus.member_group_id;
		vueOrderItems.member_group_discount_rate = (typeof(thePCStatus.member_group_discount_rate) == 'undefined' || thePCStatus.member_group_discount_rate == null) ? 0 : thePCStatus.member_group_discount_rate;
		vueOrderItems.items = [];

		vueGlobal.pageType = "Shop";
		vueGlobal.showBottom = false;

		$('input#search-product').keyup(function(e){
			let new_search = $(this).val();
			that.change_group(vueProductGroupList.current_group_id, new_search);
		});
		
		//$('#payment-table').html(tmpl('tmpl-payment-method'));
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	};

	// -3 = all, -4 = promoted
	this.change_group = function(group_id, search = '') {
		that.current_group_id = group_id;
		vueProductGroupList.current_group_id = group_id;

		if (group_id == -2) {
			$('#shop_cart').hide();
			$('#shop_cart_gift').show();
			this.gift_cart_refresh();
		}
		else {
			$('#shop_cart').show();
			$('#shop_cart_gift').hide();
			this.cart_refresh();
		}

		$('input#search-product').val(search);
		that.filtered_items = [];
		theProductList.forEach(function(obj) {

			if (group_id == -4) {
				if(typeof(obj.product_is_promoted) == 'undefined' || obj.product_is_promoted == false)
					return;
			} else if (group_id != -3) {

				if (group_id == -2 && parseFloat(obj.product_coin_price) <= 0)
					return;

				if (group_id != -2 && obj.product_group_id != group_id)
					return;
			}

			// don't show 0 stock
			if (obj.product_unlimited == 0 && obj.product_qty <= 0)
				return;

			if (obj.product_group_id == -1) {
				// pc group, member group
				var pc_group_id = (typeof(thePCStatus.pc_group_id) == 'undefined' ? 0 : thePCStatus.pc_group_id);
				var member_group_id = (typeof(thePCStatus.member_group_id) == 'undefined' ? 0 : thePCStatus.member_group_id);
				if (JSON.parse(obj.product_pc_groups).indexOf('0') < 0 && JSON.parse(obj.product_pc_groups).indexOf(pc_group_id.toString()) < 0)
					return;

				if (JSON.parse(obj.product_member_groups).indexOf('0') < 0 && JSON.parse(obj.product_member_groups).indexOf(member_group_id.toString()) < 0)
					return;

				// empty or "7|1|2|3|4|5|6"
				var todayAvailable = true;
				var yesterdayAvailable = true;
				var product_show_weekday = (typeof(obj.product_show_weekday) != 'undefined' ? obj.product_show_weekday : '');
				if (product_show_weekday.length > 0) {
					var weekdays = product_show_weekday.split('|');
					if (weekdays.indexOf(moment().format('E')) < 0)
						todayAvailable = false;
					if (weekdays.indexOf(moment().add(-1, 'days').format('E')) < 0)
						yesterdayAvailable = false;
					if (!todayAvailable && !yesterdayAvailable)
						return;
				}

				// empty or 00:00-24:00
				var product_show_time = (typeof(obj.product_show_time) != 'undefined' ? obj.product_show_time : '');
				if (product_show_time.length > 0) {
					var times = product_show_time.split('-');
					if (times.length != 2)
						return;

					var begin_times = times[0].split(':');
					var end_times = times[1].split(':');
					if (begin_times.length != 2 || end_times.length != 2)
						return;

					var begin = moment().set({ 'hour': parseInt(begin_times[0]), 'minute': parseInt(begin_times[1]), 'second': 0 });
					var end = moment().set({ 'hour': parseInt(end_times[0]), 'minute': parseInt(end_times[1]), 'second': 0 });
					if (end >= begin) {
						if (!todayAvailable)
							return;
						if (begin.isAfter() || end.isBefore())
							return;
					}

					// if like 23:00-08:00 over mid-night
					if (end < begin) {
						let isValid = ((begin.isBefore() && todayAvailable) || (yesterdayAvailable && end.isAfter()));
						if (!isValid)
							return;
					}
				}
			}

			if (search.length > 0 && obj.product_name.toLowerCase().indexOf(search.toLowerCase()) < 0)
				return;

			that.filtered_items.push(obj);
		});

		//$('#product-list').html(tmpl('tmpl-product', { items: that.filtered_items }));
		//translate_obj($('#product-list'));
		var items = that.filtered_items;
		var itemsNew = [];
		for (var i=0; i<items.length; i++)
		{ 
			if (theShop.current_group_id == -2 && items[i].product_coin_price <= 0) continue;
			if (theShop.current_group_id != -2 && items[i].product_price <= 0) continue;
			items[i].image = '';
			if (items[i].product_group_id === -1) { items[i].image = 'images/default-offer.jpg'; }
			if (items[i].product_group_id >= 0) { items[i].image = 'images/default-product.jpg'; }
			if (items[i].product_has_image) { items[i].image = 'posters/' + items[i].product_id + '.jpg'; }
			itemsNew.push(items[i]);
		}
		vueProducts.items = JSON.parse(JSON.stringify(itemsNew));

		if(group_id == -4) {
			let promotedProductList = [];
			for(var i=0, j = itemsNew.length; i<j; i+=4) {
				promotedProductList.push(itemsNew.slice(i, i+4))
			}
			vueHome.promotedItems = JSON.parse(JSON.stringify(promotedProductList));
		}

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	};
	
	this.cart_refresh = function() {
		vueOrderItems.total_cost = 0;
		vueOrderItems.total_tax = 0;
		vueOrderItems.total_amount = 0;
		vueOrderItems.total_discount = 0;
		vueOrderItems.member_group_id = thePCStatus.member_group_id;
		vueOrderItems.member_group_discount_rate = (typeof(thePCStatus.member_group_discount_rate) == 'undefined' || thePCStatus.member_group_discount_rate == null) ? 0 : thePCStatus.member_group_discount_rate;

		for (var i=0; i< this.order_items.length; i++)
		{
			this.order_items[i].order_cost = this.order_items[i].product_price * this.order_items[i].order_item_qty;
			var order_tax = theTax.getTaxWithPrice(this.order_items[i].product_tax_id, this.order_items[i].order_cost * (1 - vueOrderItems.member_group_discount_rate / 100.0));
			if(vueOrderItems.payment_method == PAY_METHOD_BALANCE)
				order_tax = 0;
			vueOrderItems.total_cost += parseFloat(this.order_items[i].order_cost);
			vueOrderItems.total_tax += parseFloat(order_tax);
			vueOrderItems.total_discount += parseFloat(this.order_items[i].order_cost) * vueOrderItems.member_group_discount_rate / 100.0;
			vueOrderItems.total_amount += this.order_items[i].order_cost * (1 - vueOrderItems.member_group_discount_rate / 100.0);
			if(theSettings.tax_included_in_price == 0)
				vueOrderItems.total_amount += parseFloat(order_tax);
		}
		vueOrderItems.items = JSON.parse(JSON.stringify(this.order_items));
		
		this.enable_cash = this.enable_credit_card = this.enable_balance = 1;
		
		for (var i=0; i<this.order_items.length; i++) 
		{
			var product_item = null;
			theProductList.forEach(function(obj) {
				if (obj.product_id == that.order_items[i].product_id)
					product_item = obj;
			});
			if(product_item == null)
				continue;
			if(typeof(product_item.product_group_payment_method) == 'undefined')
				continue;
			product_group_payment_method = JSON.parse(product_item.product_group_payment_method);
			product_group_payment_method = is_member_logined() ? product_group_payment_method.member : product_group_payment_method.guest;
			if(this.enable_cash && product_group_payment_method.indexOf('cash') < 0)
				this.enable_cash = 0;
			if(this.enable_credit_card && product_group_payment_method.indexOf('credit_card') < 0)
				this.enable_credit_card = 0;
			if(this.enable_balance && product_group_payment_method.indexOf('balance') < 0)
				this.enable_balance = 0;
		}

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	}
	
	this.update_item_qty = function(e) {
		var product_id = $(e.target).data('productid');
		var qty = $(e.target).val();
		qty = parseInt(qty);

		var product_item = null;
		theProductList.forEach(function(obj) {
			if (obj.product_id == product_id)
				product_item = obj;
		});
		if (product_item == null)
			return;

		if (isNaN(qty) || qty < 1)
			qty = 1;
		if (product_item.product_unlimited == 0 && qty > product_item.product_qty)
			qty = product_item.product_qty;

		that.order_items.forEach(function(obj) {
			if (obj.product_id == product_id) {
				obj.order_item_qty = qty;
			}
		});

		that.cart_refresh();
	}

	this.cart_change_qty = function(product_id, qty) {
		var order_item = null;
		var product_item = null;

		theProductList.forEach(function(obj) {
			if (obj.product_id == product_id)
				product_item = obj;
		});
		if (product_item == null)
			return false;

		that.order_items.forEach(function(obj) {
			if (obj.product_id == product_id)
				order_item = obj;
		});

		if (order_item == null && qty > 0) {
			order_item = {
				product_id: product_id,
				product_name: product_item.product_name,
				product_tax_id: product_item.product_tax_id,
				product_price: product_item.product_price,
				order_item_qty: 0,
			};
			that.order_items.push(order_item);
		}
		if (order_item == null)
			return false;

		var new_qty = order_item.order_item_qty + qty;
		for (var i=0; i<that.order_items.length; i++) {
			if (that.order_items[i].product_id == product_id) {
				that.order_items[i].order_item_qty = new_qty;
				// delete product or dec qty
				if(new_qty <= 0)
					that.order_items.splice(i, 1);
				break;
			}
		}

		this.cart_refresh();
		return false;
	};

	this.cart_clear = function() {
		this.order_items = [];
		this.cart_refresh();
	};

	this.buy = function(product_id, qty) {
		this.order_items = [];
		this.cart_change_qty(product_id, qty)
		$('.myModalBuy').modal('show');
		$('.modal-backdrop').css("opacity", "0.7");
	};
	
	this.cart_done_promote = function() {
		theShop.cart_done(true);
	}

	this.cart_done = function(buyNow = false) {

		if(vueOrderItems.payment_method == -1)
		{
			sweetAlert("", translate_string("Please choose a payment method"), "error");
			return;
		}

		var items = [];
		
		that.order_items.forEach(function(obj) {
			items.push({
				product_id: obj.product_id,
				qty: obj.order_item_qty
			});
		});

		var cmd = {
			action: 'submit_order',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'wss-server',
			data: {
				payment_method: vueOrderItems.payment_method,
				member_group_discount_rate: (typeof(thePCStatus.member_group_discount_rate) == 'undefined' || thePCStatus.member_group_discount_rate == null) ? 0 : thePCStatus.member_group_discount_rate,
				items: items
			}
		};

		CallFunction('WSSSEND ' + JSON.stringify(cmd));

		if(buyNow) {
			$('.myModalBuy').modal('hide');
		}
			
	};

	this.gift_cart_refresh = function() {
		vueGiftOrders.total_amount = 0;
		for (var i=0; i<this.gift_order_items.length; i++) 
		{
			this.gift_order_items[i].order_cost = this.gift_order_items[i].order_item_qty * this.gift_order_items[i].product_coin_price;
			vueGiftOrders.total_amount += parseFloat(this.gift_order_items[i].order_cost);
		}
		vueGiftOrders.items = JSON.parse(JSON.stringify(this.gift_order_items));
		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	}
	
	this.update_gift_item_qty = function(e) {

		var product_id = $(e.target).data('productid');
		var qty = $(e.target).val();
		qty = parseInt(qty);

		var product_item = null;
		theProductList.forEach(function(obj) {
			if (obj.product_id == product_id)
				product_item = obj;
		});
		if (product_item == null)
			return;

		if (isNaN(qty) || qty < 1)
			qty = 1;
		if (product_item.product_unlimited == 0 && qty > product_item.product_qty)
			qty = product_item.product_qty;

		that.gift_order_items.forEach(function(obj) {
			if (obj.product_id == product_id) {
				obj.order_item_qty = qty;
			}
		});

		that.gift_cart_refresh();
	};

	this.gift_cart_change_qty = function(product_id, qty) {
		var order_item = null;
		var product_item = null;

		theProductList.forEach(function(obj) {
			if (obj.product_id == product_id)
				product_item = obj;
		});
		if (product_item == null)
			return false;
		
		this.gift_order_items.forEach(function(obj) {
			if (obj.product_id == product_id)
				order_item = obj;
		});

		if (order_item == null && qty > 0) {
			order_item = {
				product_id: product_id,
				product_name: product_item.product_name,
				product_coin_price: product_item.product_coin_price,
				order_item_qty: 0
			};
			this.gift_order_items.push(order_item);
		}
		if (order_item == null)
			return false;

		// delete product or dec qty
		var new_qty = order_item.order_item_qty + qty;
		if (new_qty <= 0) {
			for (var i=0; i<this.gift_order_items.length; i++) {
				if (this.gift_order_items[i].product_id == product_id) {
					this.gift_order_items.splice(i, 1);
					break;
				}
			}
			this.gift_cart_refresh();
		}

		for (var i=0; i<this.gift_order_items.length; i++) {
			if (this.gift_order_items[i].product_id == product_id) {
				this.gift_order_items[i].order_item_qty = new_qty;
				break;
			}
		}

		this.gift_cart_refresh();
		return false;
	};

	this.gift_cart_clear = function() {
		this.gift_order_items = [];
		this.gift_cart_refresh();
	};

	this.gift_cart_done = function() {

		var items = [];
		that.gift_order_items.forEach(function(obj) {
			items.push({
				product_id: obj.product_id,
				qty: obj.order_item_qty
			});
		});

		var cmd = {
			action: 'submit_order',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'wss-server',
			data: {
				payment_method: PAY_METHOD_COIN,
				member_group_discount_rate: 0,
				items: items
			}
		};

		CallFunction('WSSSEND ' + JSON.stringify(cmd));

	};

	this.format_date = function(time) {
		var WEEKs = ["", "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
		var MONTHs = ["", "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

		var d = new Date();
		if (typeof(time) != 'undefined' && time.length > 0) {
			var cols = time.split(' ');
			if (cols.length == 2) {
				var date_fields = cols[0].split('-');
				var time_fields = cols[1].split(':');
				if (date_fields.length == 3 && time_fields.length > 3)
					d = new Date(date_fields[0], date_fields[1], date_fields[2], time_fields[0], time_fields[1], time_fields[2]);
			}
		}
		return WEEKs[d.getDay() + 1].toUpperCase() + ", " + d.getDate() + " " + MONTHs[d.getMonth()+1].toUpperCase() + " " + (d.getYear() - 100);
	}
}

function Events()
{
	var that = this;
	this.events = [];
	this.event_last_refreshed = { timestamp: 0, event_id: '' };
	this.current_opened_event_id = '';
	this.gamecode2names = [
		{ code: 'fortnite', name: 'Fortnite' },
		{ code: 'dota2', name: 'Dota 2' },
		{ code: 'csgo', name: 'CS:GO' },
		{ code: 'valorant', name: 'Valorant' },
		{ code: 'lol', name: 'League of Legends' },
		{ code: 'all', name: 'Fortnite, Dota 2, Valorant, LOL, CSGO' },
	];

	this.reset = function() {
		$('#event-banner').hide();
		$('#my-events-title').hide();
		$('#my-events').hide();
		$('#active-events-title').hide();
		$('#active-events').hide();

		that.events = [];
		that.event_last_refreshed = { timestamp: 0, event_id: '' };
	}

	this.show = function() {
		that.current_opened_event_id = '';
		vueGlobal.pageType = "Event";
		vueGlobal.showBottom = true;
	}

	this.load_list = function() {
		CallFunction("API type=event-list&v=2&token=" + thePCStatus.status_pc_token);
	}

	this.refresh = function() {
		$('#spinner').show();
		if (that.event_last_refreshed.event_id == that.current_opened_event_id && moment().unix() - that.event_last_refreshed.timestamp < 30) {
			$('#spinner').hide();
			return;
		}
		setTimeout(function() {
			$('#spinner').hide();
		},2000);
		that.event_last_refreshed = { timestamp: moment().unix(), event_id: that.current_opened_event_id };

		if (that.current_opened_event_id.length == 0) {
			that.load_list();
			return;
		}

		CallFunction("API type=event-detail&v=2&event_id=" + that.current_opened_event_id + "&token=" + thePCStatus.status_pc_token);
	}

	this.open = function(event_id) {

		vueGlobal.pageType = "EventDetail";
		vueGlobal.showBottom = false;

		that.current_opened_event_id = event_id;
		var current_event = null;
		that.events.forEach(function(obj) {
			if (obj.event_id == event_id)
				current_event = obj;
		});

		that.build_event_detail_html(event_id);

		// If detail not load
		if (typeof(current_event.members) == 'undefined') {
			$('#spinner').show();
			setTimeout(function() {
				$('#spinner').hide();
			},2000);
			CallFunction("API type=event-detail&v=2&event_id=" + event_id + "&token=" + thePCStatus.status_pc_token);
		}
	}

	this.build_event_detail_html = function(event_id) {
		var current_event = null;
		that.events.forEach(function(obj) {
			if (obj.event_id == event_id)
				current_event = obj;
		});

		// $('#games .event-detail-container .events').html(tmpl('tmpl-events', {events: [current_event], is_details_page: true}));
		vueEventsDetail.events = JSON.parse(JSON.stringify([current_event]));
		//$('#games .event-detail-container .event-buttons').html(tmpl('tmpl-event-buttons', {event: current_event}));
		vueEventButtons.event = JSON.parse(JSON.stringify(current_event));
		//$('#table-event-detail').html(tmpl('tmpl-event-detail', { event: current_event, members: (typeof(current_event.members) == 'undefined' ? [] : current_event.members) }));
		vueEventDetail.event = JSON.parse(JSON.stringify(current_event));
		vueEventDetail.members = JSON.parse(JSON.stringify(typeof(current_event.members) == 'undefined' ? [] : current_event.members));

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	}

	this.join_post = function() {
		if ($('#agreeTerms').is(":checked") == false) {
			sweetAlert("", translate_string('You must agree the terms of services before submitting.'), 'error');
			return;
		}

		var event_id = $('#joinEventForm input[name=event_id]').val();
		$('.myModalJoinEvent').modal('hide');
		$('#spinner').show();
		setTimeout(function() {
			$('#spinner').hide();
		},2000);
		CallFunction("API type=event-join&v=2&event_id=" + event_id + "&token=" + thePCStatus.status_pc_token);
	}

	this.join = function(event_id) {
		var current_event = null;
		that.events.forEach(function(obj) {
			if (obj.event_id == event_id)
				current_event = obj;
		});

		if (current_event == null)
			return;

		if (typeof(current_event.emember_member_account) != 'undefined' || current_event.event_status == 'past')
			return;

		$('#joinEventForm input[name=event_id]').val(event_id);
		$('.myModalJoinEvent').modal('show');
	}

	this.play = function(event_id) {
		var current_event = null;
		that.events.forEach(function(obj) {
			if (obj.event_id == event_id)
				current_event = obj;
		});

		if (current_event == null)
			return;

		if (typeof(current_event.emember_member_account) == 'undefined' && current_event.event_status != 'past') {
			that.join(event_id);
			return;
		}

		if (typeof(current_event.event_play_command) == 'undefined' || current_event.event_play_command.length == 0)
			return;

		CallFunction("RUN " + current_event.event_play_command);
	}

	this.build_event_list_html = function() {
		var event_banner = null;
		for (var i=0; i<that.events.length; i++) {
			that.events[i].event_status = 'active';
			if (moment(that.events[i].event_end_time_local).isBefore())
				that.events[i].event_status = 'past';
			if (moment(that.events[i].event_start_time_local).isAfter())
				that.events[i].event_status = 'upcoming';

			that.gamecode2names.forEach(function(game) {
				if (that.events[i].event_game_code == game.code) {
					that.events[i].game_name = game.name;
				}
			});

			if (that.events[i].event_in_banner)
				event_banner = that.events[i];
		}

		var my_events = [];
		var active_events = [];
		that.events.forEach(function(item) {
			if (typeof(item.emember_id) != 'undefined')
				my_events.push(item);
			if (typeof(item.emember_id) == 'undefined' && item.event_status == 'active')
				active_events.push(item);
		});

		my_events.sort((a, b) => {
			let a_status_score = 0;
			let b_status_score = 0;
			if (a.event_status === 'active')
				a_status_score = 2;
			if (a.event_status === 'upcoming')
				a_status_score = 1;
			if (b.event_status === 'active')
				b_status_score = 2;
			if (b.event_status === 'upcoming')
				b_status_score = 1;
			if (a_status_score != b_status_score)
				return b_status_score - a_status_score;

			if (moment(a.event_start_time_local).isBefore(moment(b.event_start_time_local)))
				return 1;
			return -1;
		})

		$('#event-banner').hide();
		$('#event-banner').removeClass('event-banner-fortnite');
		$('#event-banner').removeClass('event-banner-valorant');
		$('#event-banner').removeClass('event-banner-dota2');
		$('#event-banner').removeClass('event-banner-csgo');
		$('#event-banner').removeClass('event-banner-lol');
		$('#my-events-title').hide();
		$('#my-events').hide();
		$('#active-events-title').hide();
		$('#active-events').hide();

		if (event_banner != null) {
			//$('#event-banner').html(tmpl('tmpl-event-banner', {event: event_banner}));
			vueEventBanner.event = JSON.parse(JSON.stringify(event_banner));
			
			$('#event-banner').addClass('event-banner-' + event_banner.event_game_code);
			$('#event-banner').show();
		}

		if (my_events.length > 0) {
			//$('#my-events').html(tmpl('tmpl-events', {events: my_events, is_details_page: false}));
			vueEventsMy.events = JSON.parse(JSON.stringify(my_events));
			
			$('#my-events-title').show();
			$('#my-events').show();
		}

		if (active_events.length > 0) {
			//$('#active-events').html(tmpl('tmpl-events', {events: active_events, is_details_page: false}));
			vueEventsActive.events = JSON.parse(JSON.stringify(active_events));
			
			$('#active-events-title').show();
			$('#active-events').show();
		}

		PetiteVue.nextTick(() => {
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
	}

	this.rank_baseurl = function() {
		var rank_baseurl = 'https://rank.icafecloud.com';
		if (typeof(theCafe.rank_baseurl) != 'undefined')
			rank_baseurl = theCafe.rank_baseurl;
		return rank_baseurl;
	}

	this.onAPIResponse = function(api_action, response) {
		$('#spinner').hide();
		if (response.result == 0) {
			sweetAlert("", translate_string(response.message), 'error');
			return;
		}

		if (api_action.indexOf('type=event-list') >= 0) {
			that.events = response.events;
			that.build_event_list_html();
			return;
		}

		if (api_action.indexOf('type=event-detail') >= 0) {
			for (var i=0; i<that.events.length; i++) {
				if (that.events[i].event_id == response.event.event_id) {
					that.events[i] = response.event;

					that.events[i].event_status = 'active';
					if (moment(that.events[i].event_end_time_local).isBefore())
						that.events[i].event_status = 'past';
					if (moment(that.events[i].event_start_time_local).isAfter())
						that.events[i].event_status = 'upcoming';

					that.gamecode2names.forEach(function(game) {
						if (that.events[i].event_game_code == game.code) {
							that.events[i].game_name = game.name;
						}
					});

					// If current member record need push to members end
					if (that.events[i].members.length > 0 && that.events[i].emember_id && that.events[i].emember_rank > that.events[i].members[that.events[i].members.length-1].emember_rank) {
						that.events[i].members.push({
							emember_id: that.events[i].emember_id,
							emember_member_account: that.events[i].emember_member_account,
							emember_rank: that.events[i].emember_rank,
							emember_matches: that.events[i].emember_matches,
							emember_point_matches: that.events[i].emember_point_matches,
							emember_bonus: that.events[i].emember_bonus,
							emember_point: that.events[i].emember_point,
							emember_wins: that.events[i].emember_wins,
							emember_kills: that.events[i].emember_kills,
							emember_assists: that.events[i].emember_assists,
							emember_deaths: that.events[i].emember_deaths,
							emember_lasthits: that.events[i].emember_lasthits,
							license_country: that.events[i].license_country,
							license_icafename: that.events[i].license_icafename
						});
					}
					break;
				}
			}

			that.build_event_list_html();
			that.build_event_detail_html(response.event.event_id);
			return;
		}

		if (api_action.indexOf('type=event-join') >= 0) {
			if (response.result == 0) {
				sweetAlert("", translate_string(response.message), 'error');
				return;
			}

			that.event_last_refreshed = { timestamp: 0, event_id: '' };
			that.refresh();
			return;
		}
	}

}

function Rank()
{
	this.show = function() {

		let gameCode = ['fortnite', 'lol', 'dota2', 'valorant', 'csgo'];

		gameCode.forEach((type) => {

			if(vueRank.items[type] != undefined && vueRank.items[type].length > 0) {
				return;
			}

			$('#spinner').show();
			$.ajax({
				url: "https://rank.icafecloud.com/game-rank.php",
				method: "post",
				data: { action: "ajax-rank-data", game_code: type, page_size: 10, data_type: 'weekly', rank_week: 'last' },
				dataType: "json"
			  }).done(function(data) {

				if(typeof(data.items) != undefined) {
					vueRank.items[type] = JSON.parse(JSON.stringify(data.items));
				}

			  }).fail(function(xhr, status, error) {
				console.log(error);
			  }).always(function(){
				$('#spinner').hide();
			  });
			
		})

		vueGlobal.pageType = "Rank";
		vueGlobal.showBottom = false;
		vueRank.active_game = "fortnite";

		PetiteVue.nextTick(() => {
			$("#rank-carousel").carousel();
			$('#rank-carousel').on('slid.bs.carousel', function () {
				var activeItem = $(this).find('.carousel-item.active');
				vueRank.active_game = activeItem.data("game");
				$('#rank-game-logo-img').attr("src", "./images/" + vueRank.active_game + ".png")
			});
			ui_init();
			$('[data-toggle="tooltip"]').tooltip();
		});
		
	}
}

function ConvertToMember()
{
	this.init = function() {
		vueGlobal.menuButton.convertToMember = false;
		let license_convert_to_member_enable = typeof(theSettings.license_convert_to_member_enable) != 'undefined' ? theSettings.license_convert_to_member_enable : 0;
		if (license_convert_to_member_enable && is_logined() && (thePCStatus.member_group_id === MEMBER_GROUP_GUEST || thePCStatus.member_group_id === MEMBER_GROUP_PREPAID || thePCStatus.member_group_id === MEMBER_GROUP_OFFER))
			vueGlobal.menuButton.convertToMember = true;	
	}

	this.show = function() {
		$("#form-convert-member input[name=account]").val('');
		$("#form-convert-member input[name=birthday]").val('');
		$("#form-convert-member input[name=password]").val('');
		$("#form-convert-member input[name=confirm_password]").val('');
		$("#form-convert-member input[name=first_name]").val('');
		$("#form-convert-member input[name=last_name]").val('');
		$("#form-convert-member input[name=phone]").val('');
		$("#form-convert-member input[name=email]").val('');
		$('#form-convert-member button[type="submit"]').prop('disabled', false);
		$('.myModalConvertMember').modal('show');
	}

	this.submit = function() {
		var account = $("#form-convert-member input[name=account]").val();
		var birthday = $("#form-convert-member input[name=birthday]").val();
		var password = $("#form-convert-member input[name=password]").val();
		var confirm_password = $("#form-convert-member input[name=confirm_password]").val();
		var first_name = $("#form-convert-member input[name=first_name]").val();
		var last_name = $("#form-convert-member input[name=last_name]").val();
		var phone = $("#form-convert-member input[name=phone]").val();
		var email = $("#form-convert-member input[name=email]").val();

		if(account.length === 0) {
			sweetAlert("", translate_string("Account can not be empty!"), "error");
			return false;
		}
		if(password.length === 0) {
			sweetAlert("", translate_string("Password can not be empty!"), "error");
			return false;
		}
		if(confirm_password.length === 0 || password != confirm_password) {
			sweetAlert("", translate_string("The new password and confirm password do not match!"), "error");
			return false;
		}
		if(first_name.length === 0) {
			sweetAlert("", translate_string("First name can not be empty!"), "error");
			return false;
		}
		if(last_name.length === 0) {
			sweetAlert("", translate_string("Last name can not be empty!"), "error");
			return false;
		}

		$('#form-convert-member button[type="submit"]').prop('disabled', true);
		$('#spinner').show();

		var cmd = {
			action: 'convert_to_member',
			version: 2,
			type: 'request',
			from: 'client',
			target: 'wss-server',
			data: {
				account: account,
				birthday: birthday,
				password: password,
				first_name: first_name,
				last_name: last_name,
				phone: phone,
				email: email
			}
		};

		CallFunction('WSSSEND ' + JSON.stringify(cmd));
	}

	this.process_wss_package = function(packet) {
		if (packet.action != 'convert_to_member')
			return false;

		$('#spinner').hide();
		$('#form-convert-member button[type="submit"]').prop('disabled', false);

		if (packet.status == 'error') {
			sweetAlert("", translate_string(packet.data.message), "error");
			return;
		}

		$('.myModalConvertMember').modal('hide');
		return true;
	}
}

function member_register()
{
	var account = $("#form-register-member input[name=account]").val();
	var birthday = $("#form-register-member input[name=birthday]").val();
	var password = $("#form-register-member input[name=password]").val();
	var confirm_password = $("#form-register-member input[name=confirm_password]").val();
	var first_name = $("#form-register-member input[name=first_name]").val();
	var last_name = $("#form-register-member input[name=last_name]").val();
	var phone = $("#form-register-member input[name=phone]").val();
	var email = $("#form-register-member input[name=email]").val();
	
	if(password != confirm_password) {
		sweetAlert("", translate_string("The new password and confirm password do not match!"), "error");
		return false;
	}

	$('#form-register-member button[type="submit"]').prop('disabled', true);
	$('#spinner').show();

	var cmd = {
		action: 'member_register',
		version: 2,
		type: 'request',
		from: 'client',
		target: 'wss-server',
		data: {
			account: account,
			birthday: birthday,
			password: password,
			first_name: first_name,
			last_name: last_name,
			phone: phone,
			email: email
		}
	};

	CallFunction('WSSSEND ' + JSON.stringify(cmd));
}

var theConvertToMember = new ConvertToMember();

function Video()
{
	var that = this;
	
	this.stop = function(type)
	{
		var el = document.querySelector('#'+type);
		el.setAttribute('src', '');
		if(type == 'url-video')
			document.querySelector('.'+type).load();
		return;
		/*
		if(type == 'url-video')
		{
			var el = document.querySelector('.'+type)	
			el.pause();
			el.currentTime = 0;
			return;
		}
		
			
		if(type == 'youtube-video')
		{	
			var el = document.querySelector('.'+type);
			var iframe = document.getElementById('youtube-video');
			var iframeDoc = iframe.contentDocument || iframe.contentWindow.document;
			if (  iframeDoc.readyState  == 'complete' ) {			
				iframe.contentWindow.onload = function(){
					el[0].contentWindow.postMessage('{"event":"command","func":"' + 'pauseVideo' + '","args":""}', '*');
				}
				return
			}
			return;
		}
		*/
	}
	
	this.play = function(type, source, mute){
		var el = document.querySelector('.'+type)
		el.classList.toggle('d-none');
		var target = document.querySelector('.'+type+' #'+type);
		
		if(type == 'youtube-video')
		{
			that.stop('url-video');
			target.setAttribute('src' , "https://www.youtube.com/embed/"+source+"?mute="+mute+"&modestbranding=1&autohide=1&showinfo=0&controls=0&autoplay=1&loop=1&playlist="+source+"&version=3");
		}
		
		if(type == 'url-video')
		{
			that.stop('youtube-video');
			// "file:///E:/Internet%20Tools/iCafeMenu/html/videos/ad.webm"
			target.setAttribute('src', source);
			el.load();
			el.play();
		}
	}	
}

//var theVideo = new Video();
//theVideo.play('youtube-video', 'TJKTcGLfc7s', 1);
//theVideo.play('url-video', 'videos/video1.webm', 1);
var thePCInfo = {
   "pc_name" : "",
   "pc_turn_off_monitor_seconds" : 0,
   "version_date": ""
}

function set_monitor_turn_off_timeout(seconds)
{
	if (theMonitorTurnOffIntervalId != null) 
	{
		clearInterval(theMonitorTurnOffIntervalId);
		theMonitorTurnOffIntervalId = null;
	}

	if(seconds == 0)
		return;
	
	theMonitorTurnOffStartTime = new Date();
	theMonitorTurnOffIntervalId = setInterval(function() {

		if (new Date() - theMonitorTurnOffStartTime < seconds * 1000)
			return;

		theMonitorTurnOffStartTime = new Date();
		theMonitorTurnOffStartTime.setFullYear(2050,1,1);
		CallFunction("MONITOR OFF");

	}, 10000);
}

// https://github.com/vuejs/vue/issues/1963
// rebuildData plugin for jquery.data()
(function () {
	$.fn.extend({

	/**
	 *   jQuery.data() liefert ein falsches Ergebnis in Verbindung mit VueJS:
	 *   Werden Elemente dynamisch im DOM verändert, referenziert der jQuery.data()-Cache
	 *   evtl. auf Elemente, die ersetzt wurden. 
	 * 
	 *   Wurde ein [data-]-Attribut einmal über jQuery.fn.data() eingelesen,
	 *   liefert jQuery immer den gecachten Wert – auch wenn sich das Tag-Attribut
	 *   verändert hat, z.B. data-poi-uid="10" in data-poi-uid="33" geändert wurde.
	 */
		'rebuildData': function () {
			return this.each(function () {
				$(this).add($(this).find('*')).each(function () {
					var i, name, data, elem = this,
					attrs = elem && elem.attributes;

					if (elem.nodeType === 1) {
						i = attrs.length;
						var obj = {};
						while (i--) {
							if (attrs[i]) {
								name = attrs[i].name;
								if (name.indexOf("data-") === 0) {
									name = jQuery.camelCase(name.slice(5));
									var val = attrs[i].value;
									if ($.isNumeric(val)) val *= 1;
									obj[name] = val;
								}
							}
						}
						$(this).data(obj);
					}
				});
			});
		}
	});
})(jQuery);

function ui_init(translate = true)
{
	if(translate)
		translate_obj($('body'));
	$('label').bind('mouseenter', function(e){
		var target = e.target;
		if(target.offsetWidth < target.scrollWidth && !$(target).attr('title') && !$(target).attr('data-original-title'))
		{
			$(target).attr('title', $(target).text());
			$(target).attr('data-toggle', 'tooltip');
			$(target).attr('data-placement', 'bottom');
			$('[data-toggle="tooltip"]').tooltip();
		}
	});
}

function run_protect(protection_settings)
{
	if(protection_settings == null)
	{
		CallFunction('RUNSCRIPT "{tools}\\protection\\cmd\\allow.bat"');
		CallFunction('RUNSCRIPT "{tools}\\protection\\control_panel\\allow.bat"');
		CallFunction('RUNSCRIPT "{tools}\\protection\\download_file\\allow.bat"');
		CallFunction('RUNSCRIPT "{tools}\\protection\\power_button\\allow.bat"');
		//CallFunction('RUNSCRIPT "{tools}\\protection\\regedit\\allow.bat"');
		CallFunction('RUNSCRIPT "{tools}\\protection\\usb\\allow.bat"');
		return;
	}
	
	protection = JSON.parse(protection_settings);
	
	CallFunction('RUNSCRIPT "{tools}\\protection\\cmd\\' + (protection.cmd ? 'deny.bat"' : 'allow.bat"'));
	CallFunction('RUNSCRIPT "{tools}\\protection\\control_panel\\' + (protection.control_panel ? 'deny.bat"' : 'allow.bat"'));
	CallFunction('RUNSCRIPT "{tools}\\protection\\download_file\\' + (protection.download_file ? 'deny.bat"' : 'allow.bat"'));
	CallFunction('RUNSCRIPT "{tools}\\protection\\power_button\\' + (protection.power_button ? 'deny.bat"' : 'allow.bat"'));
	//CallFunction('RUNSCRIPT "{tools}\\protection\\regedit\\' + (protection.regedit ? 'deny.bat"' : 'allow.bat"'));
	CallFunction('RUNSCRIPT "{tools}\\protection\\usb\\' + (protection.usb ? 'deny.bat"' : 'allow.bat"'));
}