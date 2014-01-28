; Set date at welcome_str:
;**********************************************************
;    MicroFinder Doppler DF Set
;    Hardware design and software upgrade by Rich Harrington, KN6FW
;    Original software by Michael J. Allison, KN6ZT
;**********************************************************
;
;       TO FIND THINGS
;
;	@@write_buffered_char:			inp_process:
;	@@write_word:(r1)			low_speed_GPS:
;	@GPS_capture_flag                       LED_8_table:
;	@gps_heading				LED_do_slow:
;	bt_attract:                             main_play_not_so_good_tone:
;	Button Function Desription Strings	Parse_GPS:
;	button_calibrate:			p_calibrate:
;	button_config:				p_dial_out:
;	button_ledf:				P_lcd:
;	button_rot:				p_led_ring_do_display:
;	calibration				p_led_ring_display:
;	cli_cmd_table:				p_serial_in:
;	cmd_baud_show_19:			p_serial_output2:
;	cmd_eedump:				p_stepper_driver:
;	cmd_eeprom_restore:			raw_store:
;	cmd_opt:				read_dec_word:
;	cmd_set_calv:				read_word:
;	cmd_stepto:				rotation_table:
;	current_rotation_rate			rt_sec_uart_turn_on
;	degrees_convert:			Second serial port
;	degrees_write_s0:(r1)			send DD-Q
;	doppler_qual_0T9			serin_process2:
;	eeprom_read:				set_rotation_rate:
;	No_print:				snooper_qlevel
;	eeprom_restore:                 	strcmp:
;	filt_0_output:                  	timing_test
;	filt_1:					util_get_calibration_config:
;	filt_3:					write_buffered_char2:
;	get_config_ptr:(r0l in - r0 out)	write_buffered_char_add:(r1l)
;	gps_speed_flag        			write_dec_word_add:(r1)
;	Init_stuff:				DD_to_LED:
;	Display_8LED:				eeprom_image:
;	cmd_multd:
;
;	Things to Fix or Do
;
;	Next time disable port to turn off all LED outputs
;	Next time DD 99 or 100 to front. It makes filters easier.
;	Layout with one led at 0 degrees also makes 45 degrees one LED.
;
;	.data.w h'5770
;
;	Filter
;	Average with point within + or - 50 DD
;	LED speed control
;		if Q GT 4 then right now
;		as Q ranges from 1 to 4
;		change speed.
;		Keep the lower timer value value
;
;	GPS on second serial port
;		Build a small FIFO 15 char to allow sending %RRR.R/Q%HHH (EOL)
;		This routine will write out:
;               %RRR.R/Q%HHH			; RRR.R relitive heading
;		%RRR.R/Q			; Q     quality of bearing 0 to 9
;		If GPS pass-thur is on		; HHH   GPS heading
;						; EOL
;						; Total of 13 char
;		Echo flag part of OPT
;		Parce on fly
;			Get bearing
;			Get speed
;			Flag speed below OPT
;			Lock bearing when speed below OPT
;		Send relitive bearing Q
;
;                mov.w   #h'7ff7,r1      ; By rjh turns on extra pin
                                         ; on the Hitachi board
;                bset    #6, @r1         ; the time the led is on
;
;		mov.b	r1l,@port3_dr
;		bclr	#7,@port_6		; display on hex test
;		bset	#7,@port_6
;
;**********************************************************
;       Assembly        flags
;**********************************************************
;
;       Set this value to 1 for development, 0 to production.
DEVELOP_ASM                     .EQU    0
;       Set to 1 if you are KN6FW else 0
KN6FW                           .equ    1
;       Set to 1 if debug else 0
DEBUG_FLAG                      .equ    1
;
;       ---------------------------------------------------
;       (c) Copyright 1993-2012 AHHA! Solutions
;       All Rights Reserved
;       Cheryl L. Ham KE6GDH, Mary Adamson KE6GDD
;       Michael J. Allison KN6ZT, Rich Harrington KN6FW
;       This software is the exclusive property of AHHA! Solutions
;       and may not be used by anyone without express written
;       permission from an AHHA! Solutions company officer.
;       -------------------------------------------------------------
;       This embedded H8/300 assembly program is written to be compiled
;       with the GNU Binutils tool set.
;       Binutils is a freely available set of tools for assembly language.
;       The tool set include an assembler, preprocessor, linker, librarian,
;       debugger, and program loader.
;       The tool set is freely available in compiled and source form
;       for a variety of platforms.
;       The doppler source code is edited using the GNU Emacs editor.
;
;       CHANGE: 12-17-02
;       Assembler Avocet H8/300
;       Editor Ultraedit
;       -------------------------------------------------------------
;       * V2.0.0
;       1/6/1999 X1
;               - Start of the 2.0 upgrade. Based upon 1.1.0 port.
;               - Support for partial command strings (shortcuts)
;               - Changed EESAVE to SAVE for the command string
;               - Add sounder support, opt t & k, alarm
;               - Real time timers to support sounder
;       2/12/1999 X2
;               - Button BHLD will stop antenna rotation to prevent
;                 the doppler whine when you transmit nearby.
;               - Compass now displays on the pointer when in compass mode.
;               - Fixed get_boolean_token to accept "h"and "l"as acceptable
;                 arguments as options for "1" / "0".
;       2/17/1999 X3
;               - Add marquee mode for the 7 segment display
;               - Fix force display, add force_2display for marquee.
;               - Fix toggle_display to work with marquee
;               - Double step LEDs on ring to give effective 100 ddegree res.
;               - Fix overflow problems with quality calculation, and
;                 subtract a pedestal value from quality so only "dot"
;                 is displayed when the radio is not connected.
;               - Fixed a strobing effect on attractor LEDs
;               - Fixed shortcutting commands that end with CR, etc.
;       2/19/1999 X4
;               - Make pointer process use a new real time timer (rt_msec)
;               - Make the alarm process timer driven. Release more time to
;                 the other processes.
;       3/9/1999 X6
;               - Start using the HD6473388CG10 until plastic parts are avail.
;               - Fix REV0 sense bit to use P1.7 because it is the only
;                 one with pull up resistors.
;               - Added pointer option "opt +p"
;               - Fixed firehose mode so it doesn't lose characters
;                 during normal processing.
;               - All normal references to write_sync methods have been
;                 removed.
;               - Added GPS statement
;               - Add GPS sentence capture code to serin process
;               - Capture compass from GPS stream
;
;       4/7/1999 X7
;               - Fix BSWT to prohibit switching if the compass produces
;                 an error.
;               - Add config command, antenna config support
;               - Add antenna check routines
;
;       6/18/1999 FC1
;               - Add option A to turn on / off antenna checker
;               - Fix a bug on the PTT hold feature
;               - Make the "alarm" command an advanced command
;               - Fix rate display on seven segment display
;               - Make sure at least one configuration is enabled and active
;                 if the system is started with no flash memory.
;
;       7/16/1999 FC2
;               - Fix some issues that showed up with FC1
;               - Read word and byte are limited to too small of
;                 a RAM area (for the new chip, H8/338)
;               - Fix the hardware sense bit to use new pullup
;                 controller in the H8/338.
;
;       8/15/1999 FC4
;               - Fix a bug with double stepping the LED.
;
;       2.0.1
;       10/10/1999 Patch & bugfix
;               - Fix a bug where GPS streaming does not save properly.
;                 Fixed the code to save Mode2 word.
;               - For the antenna check routine, if there are more
;                 antennas connected than is configured an error is
;                 generated.
;               - Alarm 0 doesn't disable the alarm sounding.
;               - In F. mode loss of signal doesn't cause the
;                 LED to blink.

;       2.0.2
;       4/5/2000 Patch and bug fix
;               - Align the help strings.
;               - Accept 1200,2400,4800,9600 for arguments to "baud"
;               - Don't complain about not present 93c56 or unformatted
;                 just mention a version mismatch.
;               - Move the serial #0 out of the startup vector space
;               - Allow read/write word to deal with odd address.
;               - When performing an antenna check, slow the wait/settle
;                 time down to 250 mS so users can see the scan. Debug aid.
;               - Fix a bug on tone control when GPS is streaming in.
;       5/15/2000 Final 2.0.2 fix
;               - Use APRS snooper level for BBNG.
;       5/23/2000 Final (this time fer sure) fix
;               - Add interrupt vectors for 338 vector table
;       6/13/2000 Final-Final (this time fer-sur fer-sur)
;               - Fix bugs from RJH, spelling in help
;               - Execbtn bcal leads with EOL
;               - Make more commands shortcut to shorter strings
;               - Commands without arguments didn't print errors.
;               - Backspace on commands (at end) dont' work, i.e.
;                       "chkx<bs>" doesn't execute "chk"
;               - Write CRLF before prompt so empty RETURN on DOS
;                 machines will print newlines.

;       2.0.3
;       3/13/2001
;               - Add the save button "bsav" to the button functions
;               - Add the command "gminvel" to the command set
;               - Add the command "gretain" to the command set
;               - Save the GPS capture sentence.
;               - Added a command to alter antenna check voltages (acvoltage)

;       2.0.3 FC1
;       4/16/2001
;               - Changed ACV to 0.2 4.7 0.2 (consult with RJH)
;               - Changed GPSMinVel to 2 knots (consult with RJH)

;       2.0.3 FC3
;       4/17/2001
;               - Applied GPS retain time to GPS generated compass.
;       2.0.3 FC4
;       4/19/2001
;               - Fix GPS Compass retain time to work.
;       2.0.4-D3
;       12-17-02
;               - RJH convert to avocet asmembler
;               - Shorter faster eeprom read & write routines
;       D4
;       12-20-02
;               - Check int service routine
;                 it seems too long. With too many things to do.
;       D5
;       12-27-02
;               - Reduced isr to 3 pages
;       D6
;       12-27-02
;               - Removed hall effect compass
;               - Adding RJH filter dot routines
;       D7
;       1-1-03
;               - Cleaning button routines
;               - Found bug debounce timer does NOT work
;                       Button is sometimes missed if pushed for 100 mS
;                       and seldom seen if pushed for 7.5 mS
;                       Debounced by scan rate.
;       A1
;       1-19-03
;               - Debug changes
;       A2
;       1-23-03
;               - Clean-up EEPROM storage
;               - The ONLY place for eeprom read is at start of program
;                       if NOT forced to use defaults
;               - The ONLY place for eeprom write is from SAVE command!
;       A3
;       1-27-03
;               - Debug
;       A4
;       1-30-03
;               - Still debuging
;       A7
;       2-10-03
;               - Got ant check working again
;       A8
;               - Started to work on filters
;               - Found tbl
;
;       A9
;       2-12-03
;               - Working on rotation rate timer.  If phe / 2 insted of / 8
;               - Rotation rates can be easily changed to a lot of diff rates.
;
;       A10
;       3-21-03
;               - Working on filt_1 and filt_2
;               - Filt_2 concept by KD6DX
;               - Provide filter congig with 4 diff configs
;               - Any filter output to any display
;               - Leds, Pointer, Quick-look, Serial-out, APRS
;
;       A11
;       2003-03-21
;               - Find and fix sounder for loss of bearing
;
;       A12
;       2010-07-06
;               - Start work again
;               - Provide filter congig with 4 diff configs
;               - Any filter output to any display
;               - Leds, Pointer, Quick-look, Serial-out, APRS
;               - Change of mind
;                 - Any filter output to any display
;                 - Leds, Pointer, Quick-look, Serial-out, APRS
;                 - Pointer & LEDs by button, the rest by eeprom setup
;
;       A13
;       2011-07-06
;               - Start work again
;               - Find Button function and
;               - Make one for each display mode to switch filter modes
;               - Set it up to eeprom stor of choice on save
;       A14
;       2011-08-14
;               - Change ROT to supply the time constant to the time 7 to 50
;               - Can't do it eeprom space for calabration values
;               - Change filter to led filter and pointer filter
;               - change rel-absolute to rel-abs for leds and pointer
;       A15
;       2011-08-19
;               - Fixed Comm1 output buffer
;               - Changed rt clock from hack to PWM timer.
;               - Set Rot rate from 200Hz to 1150 Hz
;               - Debuging rot rate - led - pointer - rt clock
;               - Set-up Comm2 for bearing info out @ 19200
;
;	A2012-01-01
;		- Installed 5 ant
;		- rewrote asw calv
;	A2012-01-21
;		- changed qual to 0-9 and set qual 9 near filter max output
;		  no negitive numbers
;		- changed bars to 1 bar required for doppler to work
;		  3 bars near filter max output
;		- rewrote doppler degrees to ascii 360 degrees
;	A2012-01-26
;		- change all referance to qual to 0 to 9
;	A2012-03-03
;		- tried some filters average to front worked
;		- other two did not work
;		- LCD display
;	A2012-03-25
;		- filter 0 = raw
;		- filter 1 = raw + Q threshold
;		- filter 2 = n points the same n = 2, 4 ,6 ,8, 10 + Q
;		- filter 3 = average not crossing 180 degrees + Q
;		- filter 4 = average to front raw to rear + Q
;		- button for Q Threshold 1 thru 5
;		- button for sample size for average 48, 96,144, 192, 240
;	A2014-01-28
;		- fixed Ant 1 flag
;		- fixed hex input 0-9,A,F only
;		- added byte barring + h'FQ
;		- added 4 LED display
;
;*******************************************************************************
;
; How Buttons Work:
; Button scan routine provides a number from 1 to 16 based on button 1 to 8
; or button 1 to 8 held down.
; The button number is used as a pointer into RAM (from EEprom)
;       Find get function code from button function table.
;               mov.b   #0,r1h
;               subs    #1,r1
;       Button function # now in R1 and indexed to zero for button 1
;               mov.w   #button_1_function,r2   ; First entry in RAM button table
;               add.w   r1,r2
;               mov.b   @r2,r0l
; The default for button 4 is   .data.b FUNC_ROT .EQU   h'07   ; button_1
;
;FUNC_NOTHING:                  .EQU     h'00
;FUNC_ATTRACT:                  .EQU     h'01
;FUNC_CALIBRATE:                .EQU     h'02
;FUNC_PTR_SPEED:                .EQU     h'03
;FUNC_ACCEPT_CAL:               .EQU     h'04
;FUNC_APRS_SNOOP:               .EQU     h'05
;FUNC_PTR_ON_OFF:               .EQU     h'06
;FUNC_ROT:                      .EQU     h'07
;FUNC_HOLD:                     .EQU     h'09
;;                              .EQU     h'0A
;;                              .EQU     h'0B
;FUNC_BEARING:                  .EQU     h'0C
;FUNC_LED_SPEED:                .EQU     h'0D
;FUNC_GPS:                      .EQU     h'0E
;FUNC_CONFIG:                   .EQU     h'0F
;FUNC_CHECK_ANTENNA:            .EQU     h'10
;FUNC_DIM_LED:                  .EQU     h'11
;FUNC_BEARING_N_GPS:            .EQU     h'12
;FUNC_SAVE:                     .EQU     h'13
;FUNC_PTR_FILT                  .EQU     h'14
;FUNC_LED_FILT                  .EQU     h'15
;FUNC_PTR_ABS                   .EQU     h'16
;FUNC_LED_ABS                   .EQU     h'17
;
;FUNC_CUST_1:                   .EQU     h'71 ; WHY 71 ????
;FUNC_CUST_2:                   .EQU     h'72
;FUNC_CUST_3:                   .EQU     h'73
;FUNC_CUST_4:                   .EQU     h'74
;
;*******************************************************************************
;       MAX - MIN - LIMITS
;*******************************************************************************

ROTATION_RATES:		.equ	10

;*******************************************************************************
;       Ports Etc
;*******************************************************************************
;       pcr = Pull up control reg
;       ddr = Data direction reg
port_1:                         .EQU    h'ffb2
port_1_ddr:                     .EQU    h'ffb0
port_1_pcr:                     .EQU    h'ffac
port_2:                         .EQU    h'ffb3
port_2_ddr:                     .EQU    h'ffb1
port_2_pcr:                     .EQU    h'ffad
port_3:                         .EQU    h'ffb6
port_3_ddr:                     .EQU    h'ffb4
port_3_pcr:                     .EQU    h'ffae
port_4:                         .EQU    h'ffb7
port_4_ddr:                     .EQU    h'ffb5
port_5:                         .EQU    h'ffba
port_5_ddr:                     .EQU    h'ffb8
port_6:                         .EQU    h'ffbb
port_6_ddr:                     .EQU    h'ffb9
port_7:                         .EQU    h'ffbe
port_8:                         .EQU    h'ffbf
port_8_ddr:                     .EQU    h'ffbd
port_9:                         .EQU    h'ffc1
port_9_ddr:                     .EQU    h'ffc0

;       Serial Port Registers   Page 181

s0_recv_data:                   .EQU     h'ffdd
s0_tx_data:                     .EQU     h'ffdb
s0_serial_mode_reg:             .EQU     h'ffd8
s0_serial_cntrl:                .EQU     h'ffda
s0_serial_status_reg:           .EQU     h'ffdc
s0_bit_rate_reg:                .EQU     h'ffd9
s1_recv_data:                   .EQU     h'ff8d
s1_tx_data:                     .EQU     h'ff8b
s1_serial_mode_reg:             .EQU     h'ff88
s1_serial_cntrl:                .EQU     h'ff8a
s1_serial_status_reg:           .EQU     h'ff8c
s1_bit_rate_reg:                .EQU     h'ff89

;       My names for ports
;
;       PWM Timer is used for 2mS system clock
;       Page 171
PWM1_dtr:                       .EQU     h'ffa5
; Don't change init at reset to FF
;
PWM1_tcnt:                      .EQU     h'ffa6
; Read to find 156d for 2mS
; .1uS * 128 = 12.8uS * 156 = 1.9968 mS
;
PWM1_tcr:                       .EQU     h'ffa4
PWM1_start:                     .equ     h'BB
PWM1_reset                      .equ     h'3B
;

;       Timer  is 2mS system clock
;
;       Timer 1 is used to drive the sounder

timer_1_tcr:                    .EQU     h'ffd0
timer_1_tcsr:                   .EQU     h'ffd1
timer_1_const_A:                .EQU     h'ffd2

timer_16b_icra_h:               .EQU     h'ff98
timer_16b_icra_l:               .EQU     h'ff99

timer_16b_tcr:                  .EQU     h'ff96
timer_16b_ocrs:                 .EQU     h'ff97

;       Page 127 - Output compare register.

timer_16b_ocr_AB:               .EQU     h'ff94
timer_16b_csr:                  .EQU     h'ff91
timer_16b_tier:                 .EQU     h'ff90
timer_16b_value:                .EQU     h'ff92

analog_channel_port_0_4:        .EQU     h'ffe0
analog_channel_port_1_5:        .EQU     h'ffe2
analog_channel_port_2_6:        .EQU     h'ffe4
analog_channel_port_3_7:        .EQU     h'ffe6

analog_csr:                     .EQU     h'ffe8         ; Control and Status
analog_cr:                      .EQU     h'ffea         ; Control register

ANALOG_START_0:                 .EQU     h'20
ANALOG_START_1:                 .EQU     h'21
ANALOG_START_2:                 .EQU     h'22
ANALOG_START_3:                 .EQU     h'23
ANALOG_START_4:                 .EQU     h'24
ANALOG_START_5:                 .EQU     h'25
ANALOG_START_6:                 .EQU     h'26
ANALOG_START_7:                 .EQU     h'27

ANALOG_TRIGGER_DIS:             .EQU     h'7f
ANALOG_START_BIT5:              .EQU     5
ANALOG_FINISH_BIT7:             .EQU     7

QUALITY_PEDESTAL_VALUE:         .EQU     5

; ----------------------------------------------------------------------------
; EVAL BOARD VS. Production Ports

;       These ports are on the EVAL board.


button_in_dr:                   .EQU    port_8
button_com_rev0:                .EQU    4
button_com_rev1:                .EQU    6

;       PTT Bit

ptt_port:                       .EQU    port_7
PTT_BIT:                        .EQU    5

hardware_version_port:          .EQU    port_1

;       For these symbols, EB is the value used for the evaluation board.
;                          PB is the value used for the production board.
; *************************************************************************

        %IF DEVELOP_ASM
led_port:                       .EQU    h'7ff4
tenna_port:                     .EQU    h'7ff5
port3_dr:                       .EQU    h'7ff6

        %ELSE
led_port:                       .EQU    port_1
tenna_port:                     .EQU    port_2
port3_dr:                       .EQU    port_3
button_ddr:                     .EQU    port_3_ddr
;
        %ENDIF

; *************************************************************************

tenna_port_ddr:                 .EQU    port_2_ddr
led_ddr:                        .EQU    port_1_ddr
pointer_ddr:                    .EQU    port_9_ddr

;radiator_port:                 .EQU    h'ffc1
FILT_3_BAD_MAX:			.EQU	100

;       Bit rate ( table 9-3 page 194)

;       For `19.6608 Mhz
BIT_RATE_1200:                  .EQU     255       ; error 0
BIT_RATE_2400:                  .EQU     127       ; error 0
BIT_RATE_4800:                  .EQU     63        ; error 0
BIT_RATE_9600:                  .EQU     31        ; error 0
BIT_RATE_19200:                 .EQU     15        ; error 0
BIT_RATE_38400:                 .EQU     7         ; error 0

led_delay_initlower:            .EQU     500
snooper_delay_init:             .EQU     60
;
POINTER_DELAY_SCREAMER:         .EQU     16	; P5
POINTER_DELAY_FASTER:           .EQU     37
POINTER_DELAY_FAST:             .EQU     58
POINTER_DELAY_MED:              .EQU     79
POINTER_DELAY_SLOW:             .EQU     100	; P1
;
POINTER_DELAY_IDX_MIN:          .EQU     0	; P1
;
POINTER_DELAY_FAST_IDX:         .EQU     2	; P3
;
POINTER_DELAY_IDX_MAX:          .EQU     4	; P5
;
POINTER_DELAY_INIT:             .EQU     POINTER_DELAY_FAST
POINTER_DELAY_IDX_INIT:         .EQU     POINTER_DELAY_FAST_IDX
;
;       LED delays, mostly like POINTER, but add instantaneous
;	
LED_speed_MIN:                  .EQU     0	; L0 lowest, L1, L2, L3 instant
LED_speed_MAX:                  .EQU     6	; L4 lowest with Q, L5, L6
LED_speed_INIT:                 .EQU     3
;
LED_DELAY_SLOW:                 .EQU     48	; L0, L4
LED_DELAY_MED:                  .EQU     16	; L1, L5
LED_DELAY_FAST:                 .EQU     8	; L2, L6
LED_DELAY_INSTANT:              .EQU     0	; L3
;
LED_DELAY_INIT:                 .EQU     LED_DELAY_INSTANT
;
LAST_ROT:                       .equ    9
;
;       Sounder timer
;       Produce square wave from timer

timer_1_tcr_val:                .EQU     h'0a   ;  phi/64 compare and clear on A
timer_1_tcr_off:                .EQU     h'00   ;  turn off the timer/sounder
timer_1_tcsr_val:               .EQU     h'03   ;  toggle the output
;
;       Sounder frequencies
;
;sounder_500hz:                  .EQU     h'7f
;sounder_1000hz:                 .EQU     h'3f
;sounder_1500hz:                 .EQU     h'2a
;sounder_2000hz:                 .EQU     h'1f
;sounder_2500hz:                 .EQU     h'0c
;
;       Gives Various rates with the 16 Mhz clock
;       Clock is phi = crystal/2
;       Phi is / 2
;       Timer count is realy one more than entered
;       Timer toggles output on compare = x/2
;       Example: of Rotation rate 3
;       16 MHz / 2 = 8 MHz / 2 = 4 Mhz
;       4 MHZ / ( 23 + 1 ) = 167 kHZ / 2 = 83.5 kHz or 417.5 Hz
;       Clock for filter ( Rotation rate ) 200 times rotation rate
;
timer_16b_tcr_val:              .EQU    h'0f
timer_16b_ocrs_val:             .EQU    h'00
timer_16b_ocrs_final:           .EQU    h'10
timer_16b_icra:                 .EQU    h'ff98
;
;       Make us reset on compare values
timer_16b_crs_val:              .EQU    h'ff
;
;       Timer Interupt Enable values
timer_interrupt_val:            .EQU    h'04

;       Misc inputs, timer clock (16bit)
;       Control for EEPROM interface.

port_6_ddr_val:                 .EQU    h'ba

;       EEPROM Bit definitions

eeprom_clk_mask:                .EQU    h'08
eeprom_chip_select_mask:        .EQU    h'10
eeprom_data_in_mask:            .EQU    h'20

eeprom_data_out_mask:           .EQU    h'40
eeprom_data_out_bit:            .EQU    6

eeprom_cmd_read:                .EQU    h'02
eeprom_cmd_write_enable:        .EQU    h'00
eeprom_cmd_write:               .EQU    h'01
eeprom_cmd_write_all:           .EQU    h'00
eeprom_cmd_write_disable:       .EQU    h'00
eeprom_cmd_protect_enable:      .EQU    h'00
eeprom_cmd_protect_clear:       .EQU    h'03

eeprom_addr_write_enable:       .EQU    h'c3
eeprom_addr_write_all:          .EQU    h'40
eeprom_addr_write_disable:      .EQU    h'0b
eeprom_addr_protect_enable:     .EQU    h'cf

;       Bit 2 of the timer_16b_csr, to clear the compare during interrupt

timer_16b_ocfb:                 .EQU     2

; ----------------------------------------------------------------------------

;       Serial Mode = Async (0), 8bit (0), noparity (0), parity even (0),
;                     1 stop bit (0), clk sense (00)

;serial_mode_val:                .EQU     h'00

;       Serial Control = tx int (0), rx int (0), tx en (1), rx en (1),
;                        mpie (0), teie (0), int clock (0), out clk (0)

;serial_status_val:              .EQU     h'30

;       Serial Mask bits
tx_ready_bit:                   .EQU     7
tx_data_empty_bit:              .EQU     2
rx_ready_bit:                   .EQU     6
RX_OVERRUN_BV:                  .EQU     5
RX_FRAME_ERR_BV:                .EQU     4
RX_PARITY_ERR_BV:               .EQU     3
RX_ERR_BITS_MV:                 .EQU     h'38

LF:                             .EQU     h'0A
CR:                             .EQU     h'0d
ASCI_CANCEL:                    .EQU     h'18


;       This is the amount of time the calibrate routine will wait
;       until it switches to the next rotation rate. This is somewhat
;       arbitrary, but was picked to work.

CALIBRATION_WAIT_VALUE: .EQU     h'0F00

;       How long the antenna checker will wait for signals
;       to settle. This is picked to allow caps to charge in switch
;       Value is in miliSeconds

ANTENNA_CHECK_WAIT_250:         .EQU     250
ANTENNA_CHECK_SHORT_WAIT_10:    .EQU     10

;       Voltages too low or too high indicate broken switcher
ANTENNA_CHECK_TOO_LOW:          .EQU    15      ; 0.2 volts
ANTENNA_CHECK_TOO_HIGH:         .EQU    244     ; 4.8 volts
ANTENNA_CHECK_SAME_DELTA:       .EQU    14      ; 0.2 volts delta elt to elt

;       Provides about the right time period to show 7 segment leds. Will
;       turn off the the 7 segment display after this times out.

LED_7SEG_MAGIC_TIMER_NUMBER:    .EQU     h'3e7a
LED_7SEG_MAGIC_HALF_TIMER:      .EQU     h'1f3d
LED_7SEG_MAGIC_THIRD_TIMER:     .EQU     h'14d3

;       Unused LED location. This lets the doppler turn off all of the
;       LED displays.

LED_UNUSED_LOCATION:            .EQU    h'32

;       LED segment id values.

SEG7_A:                         .EQU     56
SEG7_B:                         .EQU     57
SEG7_C:                         .EQU     58
SEG7_D:                         .EQU     59
SEG7_E:                         .EQU     60
SEG7_F:                         .EQU     61
SEG7_G:                         .EQU     62
SEG7_DOT:                       .EQU     63

;       Pattern Ids

SEG_PAT_0:                      .EQU    0
SEG_PAT_1:                      .EQU    1
SEG_PAT_2:                      .EQU    2
SEG_PAT_3:                      .EQU    3
SEG_PAT_4:                      .EQU    4
SEG_PAT_5:                      .EQU    5
SEG_PAT_6:                      .EQU    6
SEG_PAT_7:                      .EQU    7
SEG_PAT_8:                      .EQU    8
SEG_PAT_9:                      .EQU    9
SEG_PAT_A:                      .EQU    10
SEG_PAT_B:                      .EQU    11
SEG_PAT_C:                      .EQU    12
SEG_PAT_D:                      .EQU    13
SEG_PAT_E:                      .EQU    14
SEG_PAT_F:                      .EQU    15
SEG_PAT_G:                      .EQU    16
SEG_PAT_DASH:                   .EQU    17
SEG_PAT_BAr1:                   .EQU    18
SEG_PAT_BAr2:                   .EQU    19
SEG_PAT_BAr3:                   .EQU    20
SEG_PAT_DOT:                    .EQU    21
SEG_PAT_K1:                     .EQU    22
SEG_PAT_K2:                     .EQU    23
SEG_PAT_K3:                     .EQU    24
SEG_PAT_K4:                     .EQU    25
SEG_PAT_LOW_C:                  .EQU    26
SEG_PAT_LOW_N:                  .EQU    27
SEG_PAT_H:                      .EQU    28
SEG_PAT_S:                      .EQU    29
SEG_PAT_W:                      .EQU    30
SEG_PAT_C_DOT:                  .EQU    31
SEG_PAT_F_DOT:                  .EQU    32
SEG_PAT_P:                      .EQU    33
SEG_PAT_LOW_R:                  .EQU    34
SEG_PAT_L:                      .EQU    35
SEG_PAT_LOW_0_DOT		.EQU	36
SEG_PAT_5_DOT:                  .EQU    37
;
;       The marquee buffer only holds 4 characters

MARQUEE_SIZE:                   .EQU    4
;       Time values in mSeconds
MARQUEE_TIME_VALUE:             .EQU    1000
MARQUEE_IDLE_TIME:              .EQU    100
;       Time value is seconds
BUT_2ND_FUNCTION_TIME:          .equ    1000
;
button_debounce_timout:         .EQU    500
;
;       Antenna bits
default_antenna_sense:          .EQU    h'00
;
ASCI_BS:                        .EQU     h'08
ASCI_CTRL_R:                    .EQU     h'12
ASCI_DEL:                       .EQU     h'7F


;       These are used in "make_hex" routine. They are prerolled
;       constants for the expression  hex = char_value - "A" + 10
;                         and         hex = char_value - "a" + 10

A_F_SUB:                        .EQU     h'37
A_F_LOW_SUB:                    .EQU     h'57

CW:                             .EQU     0
CCW:                            .EQU     1

;       Mode bits - bitvalues and maskvalues
;       NOTE: The bits for NORTH and SOUTH are combined into
;             a value that checks for the four cardinal compass
;             points (0=N 1=E 2=S 3=W) if align bit is on.

;             Compass bit is turned on when normalization is happening.

;             Calibrate is turned on when antenna calibration is happening.

MODE_MAINT_NORTH_BV:            .EQU    0
MODE_MAINT_NORTH_MV:            .EQU    h'0001
MODE_MAINT_SOUTH_BV:            .EQU    1
MODE_MAINT_SOUTH_MV:            .EQU    h'0002
MODE_MAINT_ALIGN_BV:            .EQU    2
MODE_MAINT_ALIGN_MV:            .EQU    h'0004
MODE_MAINT_COMPASS_BV:          .EQU    3
MODE_MAINT_COMPASS_MV:          .EQU    h'0008
MODE_MAINT_CALIBRATE_BV:        .EQU    4
MODE_MAINT_CALIBRATE_MV:        .EQU    h'0010

;       Special combined bits for work use.

MODE_MAINT_ALIGN_VAL_MV:        .EQU     h'0003

;       Operational mode change midlevel status.

;       NOTE: Compass on means show the compass on LEDs.
;             Relative on means show relative bearing.
;             Absolute on means show absolute bearing (north relative)
;             Fast on means show unfiltered LEDs
;             Filts on means show low pass filtered leds
;             Qual on means use quality for reflection rejection
;             Hold on means stop the display.

;       Signal Window Constants

MAX_SIGNAL_WINDOW:              .EQU    100

;       Process scheduler constants.

PROCESS_STOPPED:                .EQU    0
PROCESS_RUNNING:                .EQU    1
PROCESS_RUN:                    .EQU    1       ; Alias for RUNNING
PROCESS_SLEEP:                  .EQU    2

;       Timer constants for the attractor mode

ATTRACT_INCR_TIMER:             .EQU    100
ALARM_PROCESS_TIMER:            .EQU    1000

; -------------------------------------------------------------------------

        .section code
;       Vector Segment
;
                .data.w main            ; restart vector
        %IF DEVELOP_ASM
                .data.w soft_brk        ; soft brk
        %ELSE
                .data.w start           ; soft brk
        %ENDIF
                .data.w start           ; har.data.ware brk
                .data.w start           ; nmi

                .data.w start           ; irq0
                .data.w start           ; irq1
                .data.w start           ; irq2
                .data.w start           ; irq3
                .data.w start           ; irq4
                .data.w start           ; irq5
                .data.w start           ; irq6
                .data.w start           ; irq7
;       free-running timer
                .data.w start           ; icia

;       Input capture B
                .data.w start           ; icib
                .data.w start           ; icic
                .data.w start           ; icid

;       Output comparator
                .data.w start           ; ocia
                .data.w oc1b_srvc       ; ocib
                .data.w start           ; fovi

;       8 bit timer 0
                .data.w start           ; cmioa
                .data.w start           ; cmiob
                .data.w start           ; ovio

;       8 bit timer 1
                .data.w start           ; cmioa
                .data.w start           ; cmiob
                .data.w start           ; ovio

;       dual-port RAM
                .data.w start           ; mrei
                .data.w start           ; mwei

;       serial comm 1
                .data.w start           ; eri
                .data.w start           ; rxi
                .data.w start           ; txi
                .data.w start           ; ser_tsr_empty

;       Serial port #2
                .data.w start           ; ser1_recv_err
                .data.w start           ; ser1_rec_end
                .data.w start           ; ser1_tx_end
                .data.w start           ; ser1_tsr_empty
;       analog/digital converter
                .data.w start           ; adi

;       Place jsr labels here.
;       Followed by .data.w address of routine
;       This reduces each jsr or jmp by 2 bytes

;       form:   jsr     @@write_buffered_str

write_buffered_str:
                .data.w write_buffered_str_add

writeln_buffered_str:
                .data.w writeln_buffered_str_add

write_dec_word:
                .data.w write_dec_word_add

write_buffered_char:
                .data.w write_buffered_char_add

write_word:
                .data.w write_word_add

write_byte:
                .data.w write_byte_add


;----------------------------------------------------------

        .org    h'fe            ; save space for jsr @@aa:8

;----------------------------------------------------------

;       SERIAL NUMBER: Each CPU burned will contain a unique serial number.
;       Each number is stored as 4 digit BCD.
;       Place serial_number at end of line.  Easier to edit

serial_number:  .data.w h'F001

; -------------------------------------------------------------------------

;    Code (ROM) Segment

;       Global Register usage
;       r0 - Temp / Function return value
;       r1 - Parameter
;       r2 - Parameter
;       r3 - Unassigned
;       r4 - Unassigned
;       r5 - Reserved for antenna switch machine
;       r6 - Process Descriptor Pointer
;       r7 - Stack Pointer

;       The rules for register usage are, that each subroutine
;       preseve the state of each register in the set r1-r4.
;       No subroutines may use r5 or r6 (except for read only).

;       All functions return values in register r0.
;       Arguments are usually passed in registers starting with r1
;       although some routines will use higher registers for args.
;       This is a result of historical reasons. The following code
;       routines do not need to save r1-r4 when the run:
;               processes
;               buttons
;               CLI functions

fence_core_start:
;-------------------------------------------------------------------------

        %IF    DEVELOP_ASM

;       To use software break place     .data.w h'5770  in the
;       code to get here.
;       If you want to insert the break into ram then place the instruction
;       that was replaced by h'5770 in the location NOP
;       at the end of this routine

brk_counter:    .data.w 1               ; print break N times

soft_brk:
                push    r1
                push    r0
               mov.w   @brk_counter,R1
               bne     soft_brk_1
               jmp     brk_exit        ; if count is zero
soft_brk_1:
               dec     R1L
               mov.w   R1,@brk_counter
                mov.w   #str_soft_brk,r1
                jsr     @@write_buffered_str
                mov.w   #6,r1
                add.w   r7,r1
                mov.w   @r1,r1
                subs    #2,r1           ; correct address

;       remove this to auto replace
                bra     soft_brk_no_auto

                mov.w   @soft_brk_replace,r0
                mov.w   r0,@r1
                mov.w   #0,r0
                mov.w   r0,@soft_brk_replace
soft_brk_no_auto:
                jsr     @@write_word
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str

;       Display the registors

                mov.w   #str_reg_display,r1
                jsr     @@writeln_buffered_str

                pop     r1
                push    r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                pop     r0
                pop     r1
                push    r1
                push    r0
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r2,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r3,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r4,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r5,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r6,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                mov.w   r7,r1
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char
;
                adds	#2,sp
                adds	#2,sp
                pop	r0
                subs	#2,sp
                subs	#2,sp
                subs	#2,sp			; R0L now has condition codes
                jsr	write_binary_byte
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
brk_exit:                

                pop     r0
                pop     r1
soft_brk_replace:
                nop             ; place for removed instruction

                .data.w h'56f0  ; ret from soft brk

        %ENDIF
start:
main:
                mov.w #stack,r7

; -------------------------------------------------------------------------

;       Fill RAM with Zero

; -------------------------------------------------------------------------


                mov.w   #h'32a,r0       ; RAM size / 2 + 100
                                        ; for Hitachi board
                mov.w   #0,r1
                mov.w   #fence_ram_start,r2     ; RAM start

fill_RAM_loop:
                mov.w   r1,@r2
                adds    #2,r2
                dec     r0L
                bne     fill_ram_loop
                dec     r0h
                bne     fill_ram_loop

; -------------------------------------------------------------------------

;       Move all of the init values from program
;       memory to EEPROM RAM location
;       Except the one that should be Zero
;       The RAM is all Zero now

; -------------------------------------------------------------------------
Init_stuff:
;       Button in bit, 8.4, 8.6 (input)

                mov.b   #h'AF,r0l
                mov.b   r0l,@port_8_ddr
;                
		mov.w	#4,r1
		mov.w	r1,@rt_sec_uart_turn_on
                mov.w   #eeprom_image,r5        ; From
                mov.w   #ver_number,r6          ; To
                mov.w   #eeprom_image_size,r4   ; Count
                eepmov
;
		mov.w   #str_lcd_line1,r5       ; From
                mov.w   #lcd_line1,r6           ; To
                mov.w   #lcd_length,r4   	; Count
                eepmov
                mov.w	#lcd_line1,r4
                mov.w	r4,@lcd_pointer		; set pointer to start
                mov.b	#h'81,r0l
                jsr	lcd_inst_load
;                                
                mov.w	#16,r0
		mov.w	r0,@rt_sec_init
		
		mov.b	#48,r0l
		mov.b	r0l,@current_sample_size
		mov.b	#1,r0l
		mov.b	r0l,@current_sample_number
		mov.b	#0,r0l
		mov.b	r0l,@current_Threshold
;		
;       Set up for 4800 baud @ 19.6608 MHz (page 194, table 9-3)
;
                mov.b   #BIT_RATE_4800,r0l
                mov.b   r0l,@s0_bit_rate_reg
                mov.b   r0l,@serial_rate
                mov.b   #00,r0l				; serial_mode_val
                mov.b   r0l,@s0_serial_mode_reg
                mov.b   #h'30,r0l
                mov.b   r0l,@s0_serial_cntrl
;
;       Set up for 4800 baud @ 19.6608 MHz (page 194, table 9-3)
;
                mov.b   #BIT_RATE_4800,r0l
                mov.b   r0l,@s1_bit_rate_reg
                mov.b	r0l,@serial_rate1
                mov.b   #00,r0l				; serial_mode_val
                mov.b   r0l,@s1_serial_mode_reg		; 8 bit Data
                mov.b   #h'30,r0l
                mov.b   r0l,@s1_serial_cntrl
;
init_data:



;       1.0.4 Make sure all inputs have pull ups turned on.
;       Port 7 does not support pull ups, it is not set here.
;       Port 6 is used for timers and is not set here.
;       Detailed in the H8 manual, section 5.

;       With the H8/338, pullups are controlled by the
;       pullup control register. There are only pullups
;       on ports 1, 2, and 3.

;       Hardware detection is on P1.7. If the bit is low, REV0 MF,
;       else the chip is running on a REV1 MF.

UNUSED_PORT_1:          .EQU    h'80            ; 1.7
READ_PORT_1:            .EQU    h'7f

                mov.b   #UNUSED_PORT_1,r1l
                mov.b   r1l,@port_1_pcr

                mov.b   #READ_PORT_1,r1l
                mov.b   r1l,@port_1_ddr

;       Detect the hardware version

                mov.b   @hardware_version_port,r0l
                btst    #7,r0l
                beq     hdw_version_rev_0
                mov.b   #6,r0L
                mov.b   r0L,@hdw_button_bit
                mov.b   #1,r0l
                bra     hdw_version_save
hdw_version_rev_0:
                mov.b   #4,r0L
                mov.b   r0L,@hdw_button_bit
                mov.b   #0,r0l
hdw_version_save:
                mov.b   r0l,@hardware_version

        %IF    DEVELOP_ASM
;       This is just for development. Production burn omits this code.

                mov.b   #1,r0l
                mov.b   r0l,@hardware_version
                mov.b   #6,r0L
                mov.b   r0L,@hdw_button_bit
        %ENDIF


;       If this is a reset, turn off any displays so the "random" leds
;       do not appear to be turned on during reset. Seven 7 is common.

                mov.b   #LED_UNUSED_LOCATION,r0l
                mov.b   r0l,@led_port

;       Turn off stepper back lights.

                mov.b   #0,r0L
                mov.b   r0L,@h'ffc1
                mov.b   r0L,@Missed_1_flag_max

;       set-up bearing-quality bucket delay

                jsr     qsync_bucket_setup

;       For 2nd harmonic rejection, fundamental must be good
;       for at least this many times through the sample loop.

                mov.w   #20,r0
                mov.w   r0,@doppler_qual_timer
                mov.b	#0,r0l
                mov.b	r0l,@doppler_qual_fundx

                mov.w   #output_buffer,r0
                mov.w   r0,@output_buffer_Out_ptr
                mov.w   r0,@output_buffer_in_ptr
;
                mov.w   #output_buffer2,r0
                mov.w   r0,@output_buffer2_out_ptr
                mov.w   r0,@output_buffer2_in_ptr
;
		mov.w	#Input_buffer2,r0
		mov.w	R0,@Input_buffer2_ptr		; setup 4 first string
;
		mov.b 	#0,r0l				; False
		mov.b	r0l,@GPS_echo_flag
;
;       start real time clock
                mov.b   #PWM1_start,r1l
                mov.b   r1l,@PWM1_tcr
;
;       Initialize data for attract mode, should it ever be used.
;
                mov.b   #1,r0l
                mov.b   r0l,@led_dir

                mov.b   #h'ff,r0l
                mov.b   r0l,@led_ddr

;       Init the LED output pins
                mov.w   #led_delay_initlower,r0
                mov.w   r0,@led_delay

;       Damped led time value

                mov.b   #LED_speed_INIT,r0l
                mov.b   r0l,@current_LED_speed
                mov.w   #LED_DELAY_INIT,r0
                mov.w   r0,@led_delay_time_value
                mov.w   #filt_0_output,r1         ; address of first filter
                                                  ; filter output data address
                mov.w   #data_4_leds,r0
                mov.w   r1,@r0

;       Snoop starts within 1 second of the system starts keeping time.

                mov.w   #snooper_delay_init,r0
                mov.w   r0,@snooper_constant
                mov.b   #1,r0l
                mov.b   r0l,@snooper_qlevel

;       Init the buttons
        %IF DEVELOP_ASM
                mov.w	#h'7ff7,r0
		bclr	#2,@r0			; turn on all outputs
	%ELSE
		mov.b   #h'ff,r0l               ; all outputs
                mov.b   r0l,@button_ddr		; for chip only
	%ENDIF

;       Configure the Antenna Control Port

                mov.b   #h'ff,r0l
                mov.b   r0l,@tenna_port_ddr
                mov.w   #antenna_4_isr,r5


;       Set up the pointer

                mov.b   #h'fb,r0l
                mov.b   r0l,@pointer_ddr

;       Turn every thing off

                mov.b   #04,r0l
                mov.b   r0l,@h'ffc1

;       Set up the stepper motor state table

                mov.w   #stepper_table,r0
                mov.w   r0,@pointer_state

;       Initialize the pointer

                mov.w   #POINTER_DELAY_INIT,r0
                mov.w   r0,@pointer_delay
                mov.b   #POINTER_DELAY_IDX_INIT,r0l
                mov.b   r0l,@pointer_delay_idx
                mov.w   #filt_0_output,r1         ; address of first filter
                                                  ; filter output data address
                mov.w   #data_4_ptr,r0
                mov.w   r1,@r0
;
		mov.w	#data_4_lcdr,r0
		mov.w	r1,@r0
		mov.w	#data_4_lcda,r0
		mov.w	#filt_0_A_output,r1
		mov.w	r1,@r0

;       Port 6 used by timer, and misc input/output
;       This port also used for the EEPROM.

                mov.b   #port_6_ddr_val,r0l
                mov.b   r0l,@port_6_ddr

;       Set up the A/D converter, first time around.

                mov.b   #ANALOG_TRIGGER_DIS,r0l
                mov.b   r0l,@analog_cr
                mov.b   #ANALOG_START_0,r0l
                mov.b   r0l,@analog_csr

;----------------------------------------------------------

;       Set up the free run time for the BandPass

;       Gives us phi/8 and compare w/ a
;tcr reg
;       7       6       5       4       3       2       1       0
;    CMIEB   CMIEA    OVIE    CCLR1   CCLR0    CKS2    CKS1    CKS0
;       0       0       0       0       1       0       0       1
;       CMIEB   Compare-match interrupt enable
;       CMIEA   Compare-match interrupt enable
;       OVIE    Overflow interrupt enable
;       CCLR1\
;       CCLR0/  Clear on match A
;       CKS2\
;       CKS1 |  Clock internal / 2
;       CKS2/

;       Free running timers
;       Timer 0 is used to clock the MF8 chips

timer_stcr:                     .equ    h'ffc3
timer_0_tcr:                    .EQU    h'ffc8
timer_0_tcsr:                   .EQU    h'ffc9
timer_0_const_A:                .EQU    h'ffca
timer_0_tcr_val:                .EQU    h'09

;tcsr reg
;       7       6       5       4       3       2       1       0
;     CMFB    CMFA     OVF      -      OS3     OS2     OS1     OS0
;       0       0       0       0       0       0       1       1
;       CMFB    Compare match flag
;       CMFA    Compare match flag
;       OVF     Overflow flag
;
;       OS3\
;       OS2 \   No change on match B
;       OS1 /   Output inverts on match A
;       OS0/

timer_0_tcsr_val:               .EQU     h'03

;stcr reg
;       2       1       0
;      MPE    ICKS1   ICKS0
;       0       0       1
;       MPE     Serial ctrl see section 9 of hardware manual
;       ICKS1   Timer speed 0
;       ICKS0   Timer speed 1

timer_stcr_val:         .EQU     h'01

;       The timers are connected as follows:

;       8 bit timer 1 is configured to run from the phi clock / 2.
;       Since the system runs from a 16 MHz clock, the 8 bit timer
;       is running from a 4 MHz tick rate. The timer value (N) put
;       into timing constant A will give a period of (N+1) * .5 uS.

;       The 8 bit rate is 200 times the antenna rotation rate. This
;       provides enough clock for the MF8 to filter the audio, and
;       the 16 bit timer gives 200 pulse around the circle, and this
;       gives the doppler direction (when the comparator generates
;       the "capture" signal to the 16 bit timer).

                mov.b   #timer_stcr_val,r0l
                mov.b   r0l,@timer_stcr

                mov.b   #timer_0_tcr_val,r0l
                mov.b   r0l,@timer_0_tcr
                mov.b   #timer_0_tcsr_val,r0l
                mov.b   r0l,@timer_0_tcsr

;       Set up the sound generator (timer_1) for the sounder

                mov.b   #timer_1_tcr_off,r0l
                mov.b   r0l,@timer_1_tcr
                mov.b   #timer_1_tcsr_val,r0l
                mov.b   r0l,@timer_1_tcsr

;       Set up the 16 bit timer.

                mov.b   #timer_16b_tcr_val,r0l
                mov.b   r0l,@timer_16b_tcr
                mov.b   #timer_16b_ocrs_val,r0l
                mov.b   r0l,@timer_16b_ocrs
                mov.w   #199,r0
                mov.w   r0,@timer_16b_ocr_AB

;       Enable the timer states

                mov.b   #timer_16b_crs_val,r0l
                mov.b   r0l,@timer_16b_csr

;       Enable the interupt to switch antennas

                mov.b   #timer_16b_ocrs_final,r0l
                mov.b   r0l,@timer_16b_ocrs
                mov.w   #25,r0
                mov.w   r0,@timer_16b_ocr_AB

;       Enable interrupts on the timer

                mov.b   #timer_interrupt_val,r0l
                mov.b   r0l,@timer_16b_tier

;       Zero the pointer, slowly for show

                mov.w   @pointer_delay,r0
                push    r0
                mov.w   #4000,r0
                mov.w   r0,@pointer_delay
                jsr     zero_stepper    ; only called from here
                pop     r0
                mov.w   r0,@pointer_delay

;       Just before turning on interrupts, restore from the EEPROM.
;       This will write over the top of the default we have applied.



;       If the pointer option is not desired, turn off the
;       pointer related processes.

                mov.b   @ctrl_byte_Pointer_avail,r0L
                bne     init_data_pointer_check_done
                mov.b   #PROCESS_STOPPED,r0l
                mov.b   r0l,@ps_stepper_driver
                mov.b   r0l,@ps_dial_out

;       Good place to turn off motor drivers XXXX

init_data_pointer_check_done:
                mov.w   #0,r0
                mov.w   r0,@pointer_target

;       Set up the rate as restored
                jsr	eeprom_restore
                mov.b   @current_rotation_rate,r1l
                jsr     set_rotation_rate
                jsr     util_get_antenna_config
                mov.b   r0l,r1l
                jsr     set_antenna_configuration
                mov.w	#6,r0			; setup next time
		mov.w	r0,@rt_msec_lcd

                

;       Call startup hooks for patches.
;       If location is not ffff jump to the routine and exicute it and return.

                mov.w   #h'ffff,r1

                mov.w   @start_hook_1,r0
                cmp.w   r0,r1
                beq     init_try_hook_2
                jsr     @r0
init_try_hook_2:
                mov.w   @start_hook_2,r0
                cmp.w   r0,r1
                beq     init_try_hook_3
                jsr     @r0
init_try_hook_3:
                mov.w   @start_hook_3,r0
                cmp.w   r0,r1
                beq     init_try_hook_4
                jsr     @r0
init_try_hook_4:
                mov.w   @start_hook_4,r0
                cmp.w   r0,r1
                beq     init_data_exit
                jsr     @r0
init_data_exit:

                andc    #h'7f,ccr               ; TURN ON INTERUPTS

                mov.w   #h'ffff,r0
                mov.w   r0,@stack_sniffer

;       Break up the output stream depending on where it was
;       when the system was restarted.
;
		mov.b   #h'30,r0l		; start TX uart0
                mov.b   r0l,@s0_serial_cntrl
                				; start TX uart1
                mov.b   r0l,@s1_serial_cntrl
              
                mov.w   #welcome_str,r1
                jsr     @@writeln_buffered_str
;
                jsr     util_check_antenna
;
; --------------------------------------------------------------------

;    Process Scheduler
;    Round Robin the processes
;    Process table is   (in ROM):
;                       process state ptr       (address)
;                       entry point             (address)
;                       pid                     (char[4])
;                       sleep timer             (address)
;                       description string      (address)

;    The process scheduling algorithm is
;       if( process_state != PROCESS_STOPPED )
;       {
;               if( (process_state == PROCESS_SLEEP) &&
;                   (*process_timer == 0) )
;                       process_state = PROCESS_RUNNING;

;               if( process_state == PROCESS_RUNNING )
;                       run_the_process();
;       }

; pt_buttin:
;       look for user button.
;       Take care of CAL mode
;       Exicute button functions
; pt_attractor:
;       Make the LEDs flash
;pt_led_ring_disp
;       Hack snoop of bearing + quality
;       Handles diff modes absolute, relitive, compass, filtered
;       Converts filter amplitude to 0-9 quality
;       Hold
;       Error write cal util
;       Error write ant util
;       Error write bearing to serial
;pt_alarm:
;       Turns on signal loss alarm
;pt_snooper:
;       Move GPS strings to output
;       Error see serial_in
;       Does it do bearing too?
;pt_dial_out:           ; Pointer
;       Display relitive, absolute, compass
;pt_analog:
;       Reads filter raw values
;       Reads compass if
; pt_serial_in:
;       Deal with serial input streem.
;       Exicute user requests.
;               Runs commands
;       Handle GPS pass thru.
;       Error has utility routines
;pt_stepper:
;       Stepper moter driver
;       Times steps
;pt_led_driver:
;       Drives 7 seg display
;pt_calibrate:
;       Doppler cal
;pt_compass_cal:
;       Compass cal
;pt_sound_driver:
;       Test routine for sounder

;pt_end_of_table:
;       End of table mark

process_scheduler_start:                                        ; Idle Loop
                                                                ; Idle Loop
                jsr     p_serial_output                         ; Idle Loop
		jsr	p_serial_in2				; Idle Loop
                jsr     p_serial_output2                        ; Idle Loop
                                                                ; Idle Loop
                mov.w   @rt_clock_sec_change_flag,R1            ; Idle Loop
                beq     no_sec_change                           ; Idle Loop
                jsr     rt_clock_change_sec                     ; Idle Loop
                						; Idle Loop
no_sec_change:                                                  ; Idle Loop
                mov.b   @ant_one_flag,r1L                      	; Idle Loop
                cmp.b	#2,r1l					; Idle Loop
                bne     ant_1_exit                              ; Idle Loop
;               bra     ant_1_ok                                ; Idle Loop
;       ant_one_flag gt 1                                       ; Idle Loop
;missed_ant_1:                                                  ; Idle Loop
;                mov.b   @Missed_1_flag_max,r1H                 ; Idle Loop
;                cmp     R1L,r1H                                ; Idle Loop
;                bcs     ant_1_ok                               ; Idle Loop
;                mov.b   r1L,@Missed_1_flag_max			; Idle Loop
;                                                               ; Idle Loop
;                mov.w   #str_error_ant_1,r1                    ; Idle Loop
;                jsr     @@writeln_buffered_str                 ; Idle Loop
;								; Idle Loop
ant_1_ok:							; Idle Loop
                mov.b   #0,r1L          ; Reset flag            ; Idle Loop
                mov.b   r1L,@ant_one_flag                       ; Idle Loop
                jsr     qsync_bucket_in                         ; Idle Loop
                                                                ; Idle Loop
                jsr     process_filters                         ; Idle Loop
ant_1_exit:                                                     ; Idle Loop
                mov.w 	#process_table,r6			; Idle Loop
                                                                ; Idle Loop
process_scheduler:
;pt_lcd:      	 .data.w         ps_lcd		; init_process (byte)
;                .data.w         p_lcd		; location of code
;                .sdata  "blcd"
;                .data.w         rt_msec_lcd	; timer 
;                .data.w         pstr_lcd	; .sdataz "lcd display"
                                              			; Idle Loop
                                                                ; Idle Loop
                mov.w   @r6+,r1         ; Get process state ptr ; Idle Loop
                                        ; (points to RAM)       ; Idle Loop
                mov.w   @r6+,r0         ; Get entry point       ; Idle Loop
                                                                ; Idle Loop
                adds    #2,r6           ; Skip past PID         ; Idle Loop
                adds    #2,r6           ; Skip past PID 4bytes  ; Idle Loop
                mov.w   @r6+,r2         ; Get sleep timer       ; Idle Loop
                                        ; may need it later     ; Idle Loop
                adds    #2,r6           ; Skip past desc stringptr
                                                                ; Idle Loop
;       r6 points to next entry.                                ; Idle Loop
                                                                ; Idle Loop
                mov.b   @r1,r3l         ; Get the process state ; Idle Loop
                beq     next            ; Stopped process       ; Idle Loop
                cmp.b   #PROCESS_SLEEP,r3l                      ; Idle Loop
                bne     process_check_for_run                   ; Idle Loop
                                                                ; Idle Loop
;       Handle sleeping processes.                              ; Idle Loop
;       If the timer is expired, run the process.               ; Idle Loop
                                                                ; Idle Loop
                mov.w   @r2,r4                                  ; Idle Loop
                bne     next    ; Timer has not expired,        ; Idle Loop
                                ; process not elegible to run   ; Idle Loop
                mov.b   #PROCESS_RUNNING,r3l                    ; Idle Loop
                mov.b   r3l,@r1                                 ; Idle Loop
                                                                ; Idle Loop
process_check_for_run:                                          ; Idle Loop
                                                                ; Idle Loop
                cmp.b   #PROCESS_RUNNING,r3l                    ; Idle Loop
                bne     next                                    ; Idle Loop
                                                                ; Idle Loop
;       process is running, let's run it                        ; Idle Loop
                                                                ; Idle Loop
process_run_it:                                                 ; Idle Loop
                jsr     @r0     ; jump to routine               ; Idle Loop
                                ; return here when complete     ; Idle Loop
next:                                                           ; Idle Loop
;       Test for mS change.  If so handle change                ; Idle Loop
                                                                ; Idle Loop
;                mov.w   @rt_clock_mS_change,R1                 ; Idle Loop
;                beq     no_clock_change                        ; Idle Loop
                jsr     rt_clock_update                         ; Idle Loop
no_clock_change:                                                ; Idle Loop
                                                                ; Idle Loop
                mov.w @r6,r1    ; Test next entry for end of table
                mov.w #h'ffff,r2                                ; Idle Loop
                cmp.w r2,r1                                     ; Idle Loop
                bne process_scheduler                           ; Idle Loop
                                                                ; Idle Loop
;       Restart at the begining of the list.                    ; Idle Loop
                                                                ; Idle Loop
                jmp process_scheduler_start                     ; Idle Loop
                                                                ; Idle Loop
fence_core_end:

; --------------------------------------------------------------------
;
;    Processes
;
; -------------------------------------------------------------------------
;
fence_process_start:
;
;	place info on 2X16 lcd display
;
;	RS 0 =  Instruction Reg    1 = Data reg
;		Write only
;	  ______ _______________________________________ ______
;	RS______X_______________________________________X______  P80
;	   _____ _______________________________________ ______
;	R/W_____X_______________________________________X______  P81
;		 |		  |	450 min	     |
;		 | 1 instruction  |  3 instructions  |  3 instructions  |
;		 |   140nS min    |__________________|                  |
;	E_________________________/                  \___________P82____/
;                                         | 190 min  |   | < 10
;					  | 1 inst   |   |
;	    _____________________________ |_____________ |_____
;	D0-7_____________________________X__valid_______X______  P30
;
				; nz = busy
;
;
;	At 19.6608 crystal T state = 100 nS typical instruction = 200 nS
;       
;	RS   R/W        Operation
;	 0    0    IR write
;	 0    0 0000 0001 Clear display set DD address to 0	1.64 mS
;	 0    0 0000 001X DD address to 0			1.64 mS
;	 0    0 0000 01IS Entry mode I = Inc or Dec S = Shift
;	 0    0 0000 1DCB Display Ctrl D = on-off C = cursor B = Blink
;	 0    0 0001 SRXX Move cursor S = ? L = left-right
;	 0    0 01aa aaaa Set CG RAM address
;	 0    0 1aaa aaaa Set DD RAM address
;
;	 0    1    Busy flag read data bit 7
;	 1    0	   Data write
;	 1    1    Data read
;
;	Comand		Data Address		; Comands msb = 1
;   Line1   80 | 00 01 02 03 04 05 06 07 08 09 0A 0B 0C 0D 0E 0F
;   Line2   C0 | 40 41 42 43 44 45 46 47 48 49 4A 4B 4C 4D 4E 4F
;	    FF
;
P_lcd:
		mov.w	@rt_msec_lcd,r0
		beq	p_lcd_run
		rts
p_lcd_run:		
		mov.w	#60,r0			; setup next time
		mov.w	r0,@rt_msec_lcd
		mov.b	@current_rotation_rate,r0l
		or	#h'30,r0l
		mov.b	r0l,@lcd_rot
		mov.b	@doppler_qual_0T9,r0l
                or	#'0',r0l
                mov.b	r0l,@lcd_qualty
                mov.b   @pointer_abs_flag,r0l   ; rel = 0
                cmp.b	#0,r0l
                beq	its_rel_ptr
                mov.b	#'A',r0l
                bra	place_ptr_ar
its_rel_ptr:
		mov.b	#'R',r0l
place_ptr_ar:
		mov.b	r0l,@lcd_pointer_state
		mov.b	@current_ptr_filter,r0l
		or	#'0',r0l
		mov.b	r0l,@lcd_pointer_state+1
;		
                mov.b   @led_abs_flag,r0l   	; rel = 0
                cmp.b	#0,r0l
                beq	its_rel_led
                mov.b	#'A',r0l
                bra	place_led_ar
its_rel_led:
		mov.b	#'R',r0l
place_led_ar:
		mov.b	r0l,@lcd_led_state
		mov.b	@current_led_filter,r0l
		or	#'0',r0l
		mov.b	r0l,@lcd_led_state+1
		mov.b	@current_lcda_filter,r0l
		or	#'0',r0l
		mov.b	r0l,@lcd_afilt
		mov.b	@current_lcdr_filter,r0l
		or	#'0',r0l
		mov.b	r0l,@lcd_rfilt
;
                mov.w   @data_4_lcda,r0		; get address to data
                mov.w   @r0,r1                  ; get data
;
                jsr	degrees_convert
                push	r2
                mov.w	#lcd_abearing,r2
                mov.b	r1l,@r2
                adds	#1,r2
                mov.b	r1h,@r2
                adds	#1,r2
                mov.b	r0l,@r2
                pop	r2                
;                
;	Doppler degree (0-199)passed in r1 convert to 4 ascii (0-360)
;	ret with ascii in r0l =  100s
;			  r0h =   10s
;			  r1l =    1s
;			  r1h = 1/10s
;
;
                mov.w   @data_4_lcdr,r0		; get address to data
                mov.w   @r0,r1                  ; get data
;
                jsr	degrees_convert
                push	r2
                mov.w	#lcd_rbearing,r2
                mov.b	r1l,@r2
                adds	#1,r2
                mov.b	r1h,@r2
                adds	#1,r2
                mov.b	r0l,@r2
                pop	r2                
;                	
	%IF DEVELOP_ASM
                mov.w	#h'7ff7,r0
		bclr	#2,@r0			; turn on all outputs
	%ELSE
		mov.b   #h'ff,r0l               ; all outputs
		mov.b   r0l,@button_ddr		; for chip only
	%ENDIF

		mov.w	@lcd_pointer,r1
		mov.b	@r1,r0l			; get data or inst 4 lcd
		adds	#1,r1
		mov.w	r1,@lcd_pointer
		btst	#7,r0l			; is it a command
						; or is it the end		
		beq	lcd_next_char
lcd_instruction:				; it's special
		cmp.b	#h'ff,r0l		; end of line?
		bne	lcd_inst_load
		mov.w	#lcd_line1,r1
		mov.w	r1,@lcd_pointer
		rts
		mov.b	@r1,r0l			; first entry is a command
		adds	#1,r1
		mov.w	r1,@lcd_pointer
;
;	Instruction write
lcd_inst_load:				; Input r0l
		cmp.b	#h'80,r0l
		beq	lcd_inst_send
		cmp.b	#h'C0,r0l
		beq	lcd_inst_send
		bclr	#7,r0l
lcd_inst_send:		
		mov.b	r0l,@port3_dr		; set  port3_dr data
		bclr	#0,@port_8              ; bclr port_8 bit 0 instruction
		bset	#2,@port_8              ; bset port_8 bit 2 e 8 T states
		nop
		nop
		nop
		bclr	#2,@port_8              ; bclr port_8 bit 2 e @ 100nS per
;		bclr	#7,@port_6		; display on hex test
;		bset	#7,@port_6
		rts								
lcd_next_char:					; Data in r0l
		mov.b	r0l,@port3_dr
		bset	#0,@port_8		; data    
		bset	#2,@port_8    		; e
		nop
		nop
		nop
		bclr	#2,@port_8    		; e do it		
p_lcd_exit:
		rts		
;
;       The serial input processor is responsible for taking an input
;       string and dispatching to the correct processing routine.
;       The lookup process is a simple linear search. No big deal
;       since the commands aren't usually used at high speed.
;       (high throughput processing during a hunt.)
;
;       This process is a critical driver and should never be turned off.
;       To do so will eliminate the possibilty of ANY serial input.
;
p_serial_in:
;       Serial Input (take input and do something w/ it)
		mov.b	@s0_serial_status_reg,r0l
                btst    #4,r0l				; framing error
                beq	serin_no_err_exit
        						; On an input err, 
							; cancel the line 
							; & start over
							; Clear recv ready bit
;
				; btst 4   #RX_FRAME_ERR_BV,@s0_serial_status_reg
				; btst 3   #RX_PARITY_ERR_BV,@s0_serial_status_reg
				; btst 5   #RX_OVERRUN_BV,@s0_serial_status_reg
;
		bclr #5,@s0_serial_status_reg   	; #RX_OVERRUN_BV,@s0_serial_status_reg
		bclr #4,@s0_serial_status_reg   	; #RX_FRAME_ERR_BV,@s0_serial_status_reg
		bclr #3,@s0_serial_status_reg   	; #RX_PARITY_ERR_BV,@s0_serial_status_reg
		bclr #6,@s0_serial_status_reg   	; #rx_ready_bit,@s0_serial_status_reg
;
                mov.b   #0,r0l
                mov.b   r0l,@inp_len
serin_no_err_exit:
		mov.b	@s0_serial_status_reg,r0l
		btst    #rx_ready_bit,r0l
                bne     serin_process
                rts


serin_process:
;----------------------------------------------------------
;       If we are doing GPS compass, deal with that
;----------------------------------------------------------
;

			
;       Get byte, buffer it
                mov.w   #inp_buf,r0
                mov.b   @inp_len,r1l
                mov.b   #0,r1h
                add.w   r1,r0				; Pointer to inbuf
                mov.b   @s0_recv_data,r2l		; get char
                and     #h'7f,r2l			; remove parity
                bclr    #rx_ready_bit,@s0_serial_status_reg	; reset
;
;       Special check to see if the user pressed the delete key.
		
                cmp.b   #ASCI_DEL,r2l
                beq     serin_delete
                cmp.b   #ASCI_BS,r2l
                bne     serin_insert

serin_delete:
                cmp.b   #0,r1l
                beq     serin_delete_done
                dec	r1l
                mov.b   r1l,@inp_len

;       R0 still points to last spot in input buff
;       This fixes a bug where erase then immediate execute
;       didn't cause the command to parse correctly.

                subs    #1,r0
                mov.b   #0,r2l
                mov.b   r2l,@r0

                mov.b   #ASCI_BS,r1l			; backup input
                jsr     @@write_buffered_char
                mov.b   #' ',r1l			; erace
                jsr     @@write_buffered_char
                mov.b   #ASCI_BS,r1l			; backup again
                jsr     @@write_buffered_char
serin_delete_done:
                rts

serin_insert:
;       if c = CONTROL_R
                cmp.b   #ASCI_CTRL_R,r2l
                bne     serin_check_other_specials
                mov.w   #inp_buf,r1

;       if trying to redo and empty command, never mind.
                mov.b   @r1,r2l
                beq     serin_no_command_to_redo
                jsr     @@write_buffered_str		; What srting?
                jmp     inp_parse_and_execute
;
serin_no_command_to_redo:
                rts

serin_check_other_specials:

;       if   c = CR
                cmp.b   #CR,r2l
;		bne     p_serial_check_lf
		beq	inp_process
;
;	Place for eep restore		
;
;       else c = LF; eat the LF, don't do anything with them.
p_serial_check_lf:
                cmp.b   #LF,r2l
                bne     p_serial_GPS_test
                rts

;       else if( (c == "$") && (inp_len == 0))
;       then is GPS passthrough
p_serial_GPS_test:
;                cmp.b   #'$',r2l
;		bne     p_serial_cancel_check
;                mov.b   @inp_len,r1l
;                bne     p_serial_cancel_check
;                
;----------------------------------------------------------
;
;                mov.b   #1,r3L				; set GPS capture flag
;                mov.b   r3L,@GPS_capture_flag
;
;----------------------------------------------------------
;       else if c = ASCI_CANCEL

p_serial_cancel_check:
                cmp.b   #ASCI_CANCEL,r2l
                bne     p_serial_normal

;       Cancel the whole line
                mov.b   #0,r0l
                mov.b   r0l,@inp_len

                mov.w   #str_cancel,r1
                jsr     @@write_buffered_str
                mov.w   #str_prompt,r1
                jmp     @@write_buffered_str
					
p_serial_normal:
                mov.b   r2l,@r0			; append user input character
                inc	r1l
		mov.b   r1l,@inp_len
; Terminate the string
                adds    #1,r0
                mov.b   #0,r2h
                mov.b   r2h,@r0			; place 0 at end

;       ECHO... ECho... echo...

serin_echo:
;		mov.b	@GPS_capture_flag,r1h
;		bne	no_GPS_echo
                mov.b   r1l,@inp_len
                mov.b   r2l,r1l
                jsr     @@write_buffered_char
;
no_GPS_echo:
;       If buffer full abort the line.
                mov.b   @inp_len,r1l
                cmp.b   #inp_max,r1l
		beq     p_serial_overrun_abort
		rts
;		jmp     serin_done

p_serial_overrun_abort:
                mov.w   #str_serin_overflow,r1
                jsr     @@write_buffered_str
                mov.w   #str_prompt,r1
                jmp     @@write_buffered_str

;       Execute the command entered by the user.
;       This command will take care of searching the
;       command table. It also handles the short-cutting
;       of the user input (2.0 feature).

inp_process:

;       If the user just pressed return, then skip.
                mov.b   @inp_len,r1l
                bne     inp_parse_and_execute
                bra     inp_done_reprompt


inp_parse_and_execute:
                mov.w   #eol_str,r1			; echo cr lf
                jsr     @@write_buffered_str
no_eol_echo:
                mov.w   #cli_cmd_table,r3
;                
; Format of cli_cmd_table               
;                .data.w cmd_str_acvoltage		; compare string
;                .data.w cmd_acvoltage			; code
;                .data.w cmd_help_acvoltage		; help string                

inp_compare_loop:
                mov.w   #inp_buf,r1
                mov.w   @r3+,r2				; @r3 now points to code
                					; r2 points to comp string
                beq     inp_process_skip                ; If routine is disabled...

;       if ( cmd ptr == h'ffff ) then end of table.
                mov.w   #h'ffff,r0
                cmp.w   r0,r2
                beq     inp_not_found

inp_cmd_cmp:
                jsr     strcmp				; input r2 master string
                					; buffer r1 to comp string
                bne     inp_process_skip

inp_process_run:
                mov.w   @r3+,r0				; @r3 now points to help string
                					; r0 points at code
                mov.w   #h'ffff,r1
                cmp.w   r0,r1
                bne     inp_process_runit

                mov.w   #str_unimplemented,r1
                jsr     @@write_buffered_str
                bra     inp_done

inp_process_runit:

                adds    #2,r3                   	; setup next set
                jsr     @r0                     	; run the command
                bra     inp_done

inp_process_skip:
                adds    #2,r3                   ; skip the entry point
                adds    #2,r3                   ; skip the help string
                bra     inp_compare_loop

inp_not_found:
;		mov.b	@GPS_capture_flag,r1l
;		bne	inp_done
                mov.w   #str_unknown_command,r1
                jsr     @@write_buffered_str

inp_done:

;       Done, clear the buffer.
                mov.b   #0,r0l
                mov.b   r0l,@inp_len

inp_done_reprompt:
;		mov.b	@GPS_capture_flag,r1l
;		bne	serin_done
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
                
                mov.w   #str_prompt,r1
                jsr     @@write_buffered_str

serin_done:
                rts
;
;----------------------------------------------------------
;
; Second serial port
; Formats
;	1. Bearing relative,quality		%RRR.R/Q
;	2. Bearing absolute,quality,time 	%AAA.A/Q/HR:MI:SE
;
;	Format 1 if no gps info else format 2
;	Assume if no gps the doppler is in a fixed location
;	with the calabration set for north               
;
;----------------------------------------------------------
;
;       Compare two strings, r1 points to test string, r2 points
;       to zero terminated constant string. Note that r1 is not
;       terminated (it may come from the input buffer). For example:
;        r1 = "ABCD EFGH" matches r2 = "ABCD" or r2 = "ABCD " or r2 = "ABC"
;       r1 = "ABCD EFGH" does not match r2 = "ABC "
;       It is likely that the command table will have blanks at the
;       end of some command strings, such as "reset ". This will make sure
;       the user types in the whole command and does not mistype a
;       string and get the wrong command.
;
;       Result is returned in the EQ flag so caller can BEQ or BNE
;
strcmp:
                push    r1
                push    r2
                push    r3
                mov.b   #0,r3l
;
strcmp_loop:
                mov.b   @r1+,r0h
                mov.b   @r2+,r0l

;       If the const string is done, the compare was successful.
                beq     strcmp_done
;
;       Force the input string to lowercase

                cmp.b   #  'A'  ,r0h
                blo     strcmp_no_convert
                cmp.b   #  'Z'  ,r0h
                bhi     strcmp_no_convert
                bset    #5,r0h

strcmp_no_convert:

;       Compare the characters.
;       Special case the short cut character for the str constant (r2)

                cmp.b   #  '*'  ,r0l
                bne     strcmp_check_shortcut
                mov.b   #1,r3l
                mov.b   @r2+,r0l

strcmp_check_shortcut:
;       If the source is a space AND we are in shortcut mode,
;       the string compare is done.

                cmp.b   #  ' '  ,r0h
;       bne     strcmp_normal_compare
                bhi     strcmp_normal_compare
                cmp.b   #1,r3l
                bne     strcmp_normal_compare
                sub.b   r0l,r0l                 ; Mark the strings as equal
                bra     strcmp_done

strcmp_normal_compare:
;       If equal, keep comparing, else leave with code.
                xor     r0h,r0l
                beq     strcmp_loop
;
;
strcmp_done:
                pop     r3
                pop     r2
                pop     r1
;
;       Before leaving, set the carry bit (==0 means strings are equal)
;               (!=0 means strings not equal)
                cmp.b   #0,r0l
                rts
;
;----------------------------------------------------------

;----------------------------------------------------------
;
;       Make a 16 bit value from 4 or (fewer) characters
;       pointed to by r2

;       Return the result in r0
;       r3 used as an accumulator

read_word:
                push    r1
                push    r3
                mov.w   #0,r3
;               
;       DIGIT 1 
;       If not whitespace or less, convert
                mov.b   @r2,r0l
                cmp.b   #  ' '  ,r0l
                bls     read_word_abort
                jsr     make_hex
                bne     read_word_abort

                mov.b   r0l,r3l
                adds    #1,r2

;       DIGIT 2
;       If not whitespace, convert
                mov.b   @r2,r0l
                cmp.b   #  ' '  ,r0l
                bls     read_word_exit
                jsr     make_hex
                bne     read_word_abort

                mov.b   #16,r0h
                mulxu   r0h,r3
                or      r0l,r3l
                adds    #1,r2

;       DIGIT 3
;       If not whitespace, convert
                mov.b   @r2,r0l
                cmp.b   #  ' '  ,r0l
                bls     read_word_exit
                jsr     make_hex
                bne     read_word_abort

                mov.b   #16,r0h
                mulxu   r0h,r3
                or      r0l,r3l
                adds    #1,r2

;       DIGIT 4
;       If not whitespace, convert
                mov.b   @r2,r0l
                cmp.b   #  ' '  ,r0l
                bls     read_word_exit
                jsr     make_hex
                bne     read_word_abort

;       The shifts and temporary work around the 8 x 8 limit on
;       the multiply. The third multiply left h'xx in r3. We need
;       to save the first digit and add it back in.

                mov.b   r3h,r1l
                shll    r1l
                shll    r1l
                shll    r1l
                shll    r1l
                mov.b   #16,r0h
                mulxu   r0h,r3
                or      r0l,r3l
                or      r1l,r3h
                adds    #1,r2

read_word_exit:
                mov.w   r3,r0
                pop     r3
                pop     r1
                orc     #h'04,ccr       ; set Z
                rts
read_word_abort:
                pop     r3
                pop     r1
                andc    #h'fb,ccr       ; clear Z
                rts

;       Take a character 0-9,A-F and turn to a hex nibble
;       Return in r0l (character pointed to by r2)
;       Set zero bit if number is OK, else clear bit.
;
make_hex:       mov.b   @r2,r0l
                cmp.b   #  '0'  ,r0l
                blo     make_hex_fail
                cmp.b   #  '9'  ,r0l
                bhi     try_hex_2
                mov.b   #  '0'  ,r0h
                bra	good_hex
;                
;       Look for range A-F, first clear lower case bit for a-f.
;
try_hex_2:
                bclr	#5,r0l		; Uper case
                cmp.b   #  'A' ,r0l
                blo     make_hex_fail
                cmp.b   #  'F' ,r0l
                bhi     make_hex_fail
                mov.b   #A_F_SUB,r0h
good_hex:               
                sub.b   r0h,r0l
                mov.b   #0,r0h		; set zero bit too.
                rts
;
make_hex_fail:
                mov.w   #bad_hex,r1
                jsr     @@write_buffered_str
                andc    #h'fb,ccr	; clear zero flag
                rts			; ERROR ret

;       Write Byte (in r1l)

write_byte_add:
                push    r3
                push    r4
                mov.b   r1l,r3l
                and     #h'f0,r3l
                mov.b   #h'00,r3h
                shlr    r3l
                shlr    r3l
                shlr    r3l
                shlr    r3l
                mov.w   #hex_table,r0
                add.w   r3,r0
                mov.w   #out_buf,r4
                mov.b   @r0,r1h
                mov.b   r1h,@r4
                adds    #1,r4

;       Second nibble

                and     #h'0f,r1l
                mov.b   #h'00,r1h
                mov.w   #hex_table,r0
                add.w   r1,r0
                mov.b   @r0,r1l
                mov.b   r1l,@r4
                adds    #1,r4
;               mov.b   # ' ' ,R1L      ; insert space at end
;               mov.b   r1l,@r4
;               adds    #1,r4
                mov.b   #0,r1l          ; Zero term
                mov.b   r1l,@r4
                mov.w   #out_buf,r1
                jsr     @@write_buffered_str

                pop     r4
                pop     r3
                rts

; -------------------------------------------------------------------------

;       Given the pointer to a string (r1), convert to a binary value
;	Ret zero set if ok
;       r0 - Return decimal value
;       r1 - input string
;       r2 - H (negative flag) L (used in multiplying)
;       r3 - accumulator
;       r4 - temp for multiplications

read_dec_word:
                push    r2
                push    r3
                push    r4
                mov.b   #0,r2h          ; flag false
                mov.w   #0,r3
                mov.b   @r1+,r0l
                cmp.b   #  '-'  ,r0l
                bne     read_dec_positive
                mov.b   #1,r2h          ; flag true
                mov.b   @r1+,r0l
read_dec_positive:
                mov.b   #  '0'  ,r0h
                cmp.b   #  '0'  ,r0l    ; check for below number
                blo     read_dec_done
                cmp.b   #  '9'  ,r0l
                bhi     read_dec_done
                sub.b   r0h,r0l         ; sub "0"
                blo     read_dec_err
                cmp.b   #9,r0l
                bhi     read_dec_err
                mov.b   #0,r0h          ; R0 = number 0-9
;       multiply accumulator by 10
                mov.w   r3,r4
                ;shal   r3l             ; 2x    2
                ;shal   r3l             ; 4x    2
                ;add.b  r4l,r3l         ; 5x    2
                ;shal   r3l             ; 10x   2
                mov.b   #10,r2l         ; 2
                mulxu   r2l,r3          ; 14
                mov.b   r4h,r4l         ; What? Have 0 ?
                beq     read_dec_add_digit
                mov.b   #0,r4h
                mulxu   r2l,r4          ; 10 times
                add.b   r4l,r3h
                bcs     read_dec_err
read_dec_add_digit:
;       add in new digit
                add.w   r0,r3
                mov.b   @r1+,r0l
                bra     read_dec_positive
read_dec_done:
                mov.w   r3,r0
                pop     r4
                pop     r3
                pop     r2
                orc     #h'04,ccr       ; set zero flag
                rts
read_dec_err:
                pop     r4
                pop     r3
                pop     r2
                andc    #h'fb,ccr       ; clear zero flag
                rts

; -------------------------------------------------------------------------
;       Write the 16 bit value contained in R1
write_word_add:
                push    r2
                mov.w   r1,r2
                mov.b   r1h,r1l
                jsr     @@write_byte
                mov.b   r2l,r1l
                jsr     @@write_byte
                pop     r2
                rts

;----------------------------------------------------------
;
;	Convert DD to LED8
;
;	Input R0l filter number
;
;	output	r01 and r0h from table or 07
;		if 07
;		r0l = 07
;		r0h = 70
;
;----------------------------------------------------------
;
DD_to_LED:
		mov.w	#filt_0_output,r1
		mov.b	#0,r0h
		shal	r0l			; Words
		add.w	r0,r1			; Now points to data
		mov.w	@r1,r0			; Now have DD from selected filter
		cmp.b	#51,r0l
		bls	DD_to_LED_table
		cmp.b	#148,r0l
		bhs	DD_to_LED_table2
		mov.b	#h'07,r0l
		bra	DD_to_LED_exit
;
DD_to_LED_table2:		
		add.b	#256 - 96,r0l		; need to adjust for entry
;						; in to table 148 becomes 52		
DD_to_LED_table:
		mov.w	#LED8_table,r1
		add.w	r0,r1
		mov.b	@r1,r0l
DD_to_LED_exit:
		mov.b	r0l,r0h
		rotr	r0h
		rotr	r0h
		rotr	r0h
		rotr	r0h
		rts							
;
;
qsync_bucket_setup:
                mov.b   #1,r1L
                mov.b   r1L,@qsync_bucket_full_flag

;       NOT full

                mov.w   #qsync_bucket_mem_start,r0
                mov.w   r0,@qsync_bucket_ptr
                rts

qsync_bucket_in:

                mov.w   @timer_16b_icra,r0      ; get raw bearing
                mov.w	r0,@raw_store
                mov.b   @calibration,r1l
                mov.b   #0,r1h               
                sub.w   r1,r0
                bcc     qsync_bucket_bearing_ok

;       Correct for underflow

                mov.w   #200,r1
                add.w   r1,r0

qsync_bucket_bearing_ok:
                mov.b   r0L,r2L
                mov.w   @qsync_bucket_ptr,r0
                mov.b   r2L,@r0                 ; Put in data
                adds    #1,r0
                mov.w   r0,@qsync_bucket_ptr
                mov.w   @qsync_bucket_end,r1
                cmp.w   r0,r1
                bne     qsync_bucket_no_ptr_correct

;       Has to rap-a-round to have output.

                mov.w   #qsync_bucket_mem_start,r0
                mov.w   r0,@qsync_bucket_ptr
                mov.b   #0,r1l
                mov.b   r1l,@qsync_bucket_full_flag

;       Now output starts.

qsync_bucket_no_ptr_correct:

                mov.b   @qsync_bucket_full_flag,r2L     ; sets flag
                mov.b   r2L,@qsync_bearing              ; sets bearing to 1
                bne     qsync_bucket_no_data            ; if empty

                mov.b   @r0,r2L
                mov.b   r2L,@qsync_bearing              ; places data

qsync_bucket_no_data:
                rts             ; Z flag = data



;-------------------------------------------------------------------------

;       Utility routine to do long divide 2 words by 1 word
;       just get a close approx
;       input   R1 and R2 Div into
;               R3       Div by
;       output  R2
;       Returns Zero flag set if div by 0

big_div_shift:
;       div by 2 each time thru
                shlr    r1h
                rotxr   r1L
                rotxr   r2h
                rotxr   r2L

                shlr    r3h
                rotxr   r3L
;       Entry
big_div_aprox:
                mov.w   R1,R1           ; set zero flag
                   bne  big_div_shift
                mov.b   r3h,r3h
                   bne  big_div_shift
big_div_doit:
                divxu   r3L,r2          ; ret zero if div by zero
                rts

; -------------------------------------------------------------------------

;       Utility routine to do long divide to prevent overflow.
;       R1 div by R0L
;       R2 =  quotient (answer)

;       Example:
;       13D / 1E = A
;       R1   = 13D
;       R0L = 1E

util_long_divide:
                mov.b   #0,r2h
                mov.b   r1h,r2l ; R2L = 01
                divxu   r0l,r2  ; 0001 / 1E = 0
                mov.b   r2h,r1h ; R1h = 01
                divxu   r0l,r1  ; 13D / 1E = A
                mov.b   r2l,r2h
                mov.b   r1l,r2l ; R2 = 000A
                rts

;-----------------------------------------------------------------------

;       Long multiply 16 x 8.
;       This routine will overflow unless careful consideration of the
;       numerical properties of the arguments is taken into account.

;       R1 =   Multiplicand (16 bit)  (mcnd)
;       R2L = Multiplier (8 bit) (mplr)

;       result = (mcnd.l * mplr)
;       result += (mcnd.h * mplr).l << 8
;
;       Example:
;               10A  x  2B = 2CAE
;       R1   = 10A
;       R2L = 2B
;       R3L = R1h = 01
;       R2L x R1        = 2B x 0A =  1AE
;       R2L x R3        = 2B x 01 =  02B
;       Values GT 00FF are sure overflow

;       R3L = R0h =  02B
;       R0   = R1 + R0 = 2B00 +1AE = 2CAE

					; 56 total
;
; ---------------------------------------------------------
;
; Write binary byte
; entry in r0l
;
; ---------------------------------------------------------
;
write_binary_byte:
		mov.b	#8,r0h
write_binary_byte_loop:		
		shal	r0l
		bcs	send_a_1
		mov.b	#'0',r1l
		jsr     @@write_buffered_char
		bra	write_binary_byte_test
send_a_1:
		mov.b	#'1',r1l
		jsr     @@write_buffered_char
write_binary_byte_test:
		dec.b	r0h
		bne	write_binary_byte_loop
		rts
;
; ---------------------------------------------------------
;
;       Write decimal 16 bit value contained in r1
write_dec_word_add:
                push    r2
                push    r3
                mov.b   #0,r2h          ; flag false
                mov.b   r2h,@temporary
                mov.w   #out_buf_end,r3
                mov.w   #0,r0
                mov.b   r0l,@-r3
                btst    #7,r1h
                beq     write_dec_positive
;       set neg flag and complement the value
                mov.b   #1,r2h          ; flag true
                mov.b   r2h,@temporary
                sub.w   r1,r0
                mov.w   r0,r1
write_dec_positive:
                mov.b   #10,r0l
                bsr     util_long_divide
                mov.b   #  '0'  ,r0l
                add.b   r0l,r1h
                mov.b   r1h,@-r3
                mov.w   #0,r0
;       restore quotient back to r1 so loop works.
                mov.w   r2,r1
                cmp.w   r0,r1
                bne     write_dec_positive
write_dec_done:
;       Tack on minus sign if needed.
                mov.b   @temporary,r2h
                beq     write_dec_no_dash
                mov.b   #  '-'  ,r0l
                mov.b   r0l,@-r3
write_dec_no_dash:
                mov.w   r3,r1
                jsr     @@write_buffered_str
                pop     r3
                pop     r2
                rts

;        Write decimal byte and pad it with spaces, if needed
;        Argument in R0L

write_padded_dec_byte:
                push    r1
                push    r2
                mov.b   #0,r0h

                mov.w   r0,r2
;       Save from being walked upon in other calls

                cmp.b   #100,r2l
                bhs     write_padded_byte_pad2
                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char

write_padded_byte_pad2:
                cmp.b   #10,r2l
                bhs     write_padded_doit
                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char

write_padded_doit:
                mov.w   r2,r1
                jsr     @@write_dec_word
                pop     r2
                pop     r1
                rts

; ---------------------------------------------------------

;       Place number in output buffer
;       convert from register values 0 to F to ascii
;       Input   r1L

write_0toF:
                and     #h'0f,r1L
                or      #h'30,r1L
                cmp.b   #h'3a,r1L
                bcs     write_buffered_char_add
                add     #7,R1l

;       falls thru to write_buffered_char_add
; ---------------------------------------------------------
;
;	Input r1l
;
;	Wait for buffer not full *********
;       If so much to print then most likley not direction finding

write_buffered_char_add:
;
;	    inc inptr (temp)
;	correct for loop
;		| ________________
;		|/                 \
;	inptr = outptr?            |
;       no		yes        |
;	|		|          |
;	|           Wait for space |
;       |               \__________/
; Place new char   
; inc inptr	`	
; correct for loop
;       
;			00FB10 	output_buffer:                  .res.b  700
;			00FDCC 	output_buffer_end:              .res.w  1
;			00FDCE 	output_buffer_in_ptr:           .res.w  1
;			00FDD0 	output_buffer_Out_ptr:          .res.w  1
;			Input char r1l		
;
                push    r2
                push    r1
                mov.w   @output_buffer_in_ptr,r2
                adds    #1,r2
                mov.w   #output_buffer_end,r1
                cmp.w   r1,r2
                bne     write_buffered_ptr_corrected
                mov.w	#output_buffer,r2                
write_buffered_ptr_corrected:
		mov.w	@output_buffer_out_ptr,r1
		cmp.w	r1,r2
		bne	write_buffered_Place_ch
		push	r2
		jsr	p_serial_output
		pop	r2
		bra	write_buffered_ptr_corrected
		
write_buffered_Place_ch:
		pop	r1
		push	r1			; recover char
		mov.w   @output_buffer_in_ptr,r2		                              
                mov.b   r1l,@r2			; Place new data
                adds    #1,r2
                mov.w   R2,@output_buffer_in_ptr
                mov.w   #output_buffer_end,r1
                cmp.w   r1,r2
                bne     write_buffered_char_add_done
                mov.w	#output_buffer,r2
                mov.w   r2,@output_buffer_in_ptr
write_buffered_char_add_done:
                pop     r1
                pop     r2
                rts

;       Write 4 characters, not null terminated to the output
;       Char String ptr in r1

write_buffered_4char:
                push    r2
                push    r3

                mov.w   r1,r3           ; Writting buffered chars uses R1
                mov.b   #4,r2h
write_buffered_4_loop:
;       Get the char, print it
                mov.b   @r3,r1l
                adds    #1,r3
                jsr     @@write_buffered_char

;       See if all characters are used up
                mov.b   #1,r0l
                sub.b   r0l,r2h
                bne     write_buffered_4_loop

;       All done
                pop     r3
                pop     r2
                rts

;       Pointer to string passed in r1
;
; ---------------------------------------------------------

write_buffered_str_add:
                push    r2
                mov.w   r1,r2
write_buffered_string_loop:
                mov.b   @r2,r1l
                adds    #1,r2
                beq     write_buffered_str_exit
                jsr     @@write_buffered_char
                bra     write_buffered_string_loop

write_buffered_str_exit:
                pop     r2
                rts

writeln_buffered_str_add:
                jsr     @@write_buffered_str
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str
;
; ---------------------------------------------------------                
;
write_buffered_char2:
;
;	inc inptr (temp)
;	correct for loop
; 	Place new char   
; 	inc inptr	`	
; 	correct for loop
;
;			00FD4A output_buffer2:                 .res.b  16
;			00FD5A output_buffer2_end:             .res.w  1
;			00FD5C output_buffer2_in_ptr:          .res.w  1
;			00FD5E output_buffer2_out_ptr:         .res.w  1
;
;			Input char r1l		        
;		
write_buffered_Place_ch2:
		push	r2
		push	r1
		mov.w   @output_buffer2_in_ptr,r2
                mov.b   r1l,@r2					; Place new data
                adds    #1,r2					; inc in ptr
                mov.w   R2,@output_buffer2_in_ptr		; save new in ptr
                mov.w   #output_buffer2_end,r1			; at the end?
                cmp.w   r1,r2
                bne     write_buffered_char_add_done2		; No
                mov.w	#output_buffer2,r2			; Reset to start
                mov.w   r2,@output_buffer2_in_ptr		; save in ptr at start of buffer
write_buffered_char_add_done2:
		pop	r1
                pop     r2
                rts
;                
; ---------------------------------------------------------
p_serial_output:

;       Only going to send characters if there any to send
;       and the output uart is ready.

                mov.w   @output_buffer_in_ptr,r1
                mov.w   @output_buffer_out_ptr,r0
                cmp.w   r0,r1
                bne     p_serial_out_send_a_char
                rts

p_serial_out_send_a_char:

                btst    #tx_ready_bit,@s0_serial_status_reg
                beq     p_serial_out_exit

;       Have a character, the UART is ready, let's do it.

                mov.b   @r0,R1l
                adds    #1,r0			; inc ptr
                mov.b   r1l,@s0_tx_data		; Send it



;       Take care of ready bit and xmitter data empty

;       This sends the character

                bclr    #tx_ready_bit,@s0_serial_status_reg


;       Check for the end of buffer 

                mov.w   #output_buffer_end,r1
                cmp.w   r0,r1
                bne     p_serial_out_save



                mov.w   #output_buffer,r0

p_serial_out_save:
                mov.w   r0,@output_buffer_out_ptr

p_serial_out_exit:
                rts
;
; ---------------------------------------------------------
;
p_serial_in2:
;       Serial Input (take input and do something w/ it)
		
		mov.b	@s1_serial_status_reg,r0l
		btst    #rx_ready_bit,r0l
                bne     serin_process2
;
;		mov.b	@s1_serial_status_reg,r0l
;                btst    #4,r0l				; framing error
;                beq	serin_no_err_exit2
        						; On an input err, 
							; cancel the line 
							; & start over
							; Clear recv ready bit
							;
		bclr #5,@s1_serial_status_reg   	; #RX_OVERRUN_BV,@s0_serial_status_reg
		bclr #4,@s1_serial_status_reg   	; #RX_FRAME_ERR_BV,@s0_serial_status_reg
		bclr #3,@s1_serial_status_reg   	; #RX_PARITY_ERR_BV,@s0_serial_status_reg
;		bclr #6,@s1_serial_status_reg   	; #rx_ready_bit,@s0_serial_status_reg
;
serin_no_err_exit2:
;		
                rts
;
serin_process2:
;----------------------------------------------------------
;       If we are doing GPS compass, deal with that
;----------------------------------------------------------
;
;       Get byte

                mov.b   @s1_recv_data,r1l		; get char
                and     #h'7f,r1l			; remove parity
                push	r1
                bclr    #rx_ready_bit,@s1_serial_status_reg	; reset
                mov.b	@GPS_echo_flag,r1h
                beq	Input_buffer_insert		; No echo
                jsr	write_buffered_char2		; Echo
                
;
Input_buffer_insert:
		pop	r1
		push	r1
		push	r0

		mov.w	@Input_buffer2_ptr,r0           ; Place char in buffer
		mov.b	r1l,@r0
		adds	#1,r0
		mov.w	r0,@Input_buffer2_ptr
		cmp.b	#h'0a,r1l			; got full string?
		bne	Input_buffer_exit		; No
		mov.w	#Input_buffer2,r0
		mov.w	R0,@Input_buffer2_ptr		; setup 4 next string
		pop	r1
		pop	r0
		bra	Parse_GPS
Input_buffer_exit:
		pop	r1
		pop	r0
		rts
;
Print_doppler_bearing:
		mov.b   #'%',r1l
                jsr     write_buffered_char2
		mov.b   @qsync_bearing,r1L
                mov.b   #0,r1h
		jsr	degrees_write_s1 
		mov.b	#'/',r1l
		jsr	write_buffered_char2
		mov.b	@doppler_qual_0T9,r1l
                or	#'0',r1l
                jsr     write_buffered_char2
                mov.b   #h'0a,r1l
                jsr     write_buffered_char2
                mov.b   #h'0d,r1l
                jmp     write_buffered_char2		
;
; ---------------------------------------------------------		
;
;
;	What we want is speed and compass heading
;	get it from $GPRMC string
;	parse $GPRMC and ignore any other strings
;$GPRMC,214151.000,A,3742.0840,N,12152.0980,W,64.13,90.76,280112,,*19
;					      SSSSS BBBBB
;$GPRMC,215522.000,A,3746.7552,N,12150.0657,W,41.50,288.75,280112,,*2A
;					      SSSSS BBBBBB
;$GPRMC,221500.000,A,3740.7032,N,12155.2404,W,0.01,5.41,280112,,*1A
;					      SSSS BBBB
;Speed in Knots (just a little faster than mile/hr)
;	$GPRMC string, speed and bearing not the same length
;	Have to find $GPRMC and then count ','s to desired fields
;	Speed after 7th ','	read only intergers and not 1/10
;	Bearing after 8th ','	read only intergers and not 1/10
;	checksum who cares
;	String ends with CR LF                
;
Parse_GPS:
;	look for ',' count them to 7 speed and 8 bearing
;	reset timer to revert to normal op
;
		mov.w   #Input_buffer2,r1
                mov.w   #str_gprmc_parse,r2
                jsr     strcmp
                beq	Got_GPRMC
                rts
Got_GPRMC:                
;
;read_dec_word:	Input r1 pointer  Return the result in r0
;
; need to find $gpmrc first

		mov.w   #input_buffer2,r1		; Starting address
		mov.b	#7,r0h				; Number of ','
GPS_parse_loop:		
		mov.b	@r1+,r0l
		cmp.b	#',',r0l
		bne	GPS_parse_loop
		dec	r0h
		bne	GPS_parse_loop
		jsr	read_dec_word			; Speed
		mov.w	r0,@GPS_speed
		
cmd_speed_loop:
		mov.b	@r1+,r0l
		cmp.b	#',',r0l
		bne	cmd_speed_loop
		jsr	read_dec_word			; Bearing
		mov.w	r0,@GPS_bearing
		jsr	gps_bearing_2_dd
		mov.w	@GPS_speed,r1
		mov.b	#0,r0h
		mov.b	r0h,@gps_speed_flag
		mov.b	@GPS_min_speed,r1h
		cmp.b	r1h,r1l
		bls	low_speed_GPS
		mov.b	r0l,@gps_speed_flag
;
low_speed_GPS:
		mov.b   @Bearing_print_flag,r0l
		beq	No_print
		jsr	Print_doppler_bearing
No_print:		
;                
;	place compass
;	on lcd                
                mov.b	@gps_heading_dd,r1l
                mov.b	#0,r1h
                push	r2
                jsr	degrees_convert
                mov.w	#lcd_comp,r2
                mov.b	r1l,@r2
                adds	#1,r2
                mov.b	r1h,@r2
                adds	#1,r2
                mov.b	r0l,@r2
                pop	r2
Not_GPRMC:                
                rts		
;
;----------------------------------------------------------
;
gps_bearing_2_dd:
;                mov.b   #1,r0L
;                mov.b   r0L,@ctrl_byte_GPS_compass_avail
;       If we ever get a gps set compass ok             

;       Since there is a compass, convert the heading to
;       doppler degrees (200 dd / 360 deg, or 5 dd/ 9 deg)

                mov.w   @gps_bearing,r0
                mov.w	r0,r1			; 2
                add.w	r0,r0			; 2 ; 2x
                add.w	r0,r0			; 2 ; 4x
                add.w	r1,r0			; 2 ; 5x                
;						Total 8
;					; 64/8	8.0 times faster
;					; and 4 instructions
                mov.b   #9,r1l
                divxu   r1l,r0
                cmp.b	#4,r0h		; less than 1/2
                bls	gps_no_add
                inc	r0l
gps_no_add:                
                cmp.b   #200,r0l
                blo     serin_no_rollover
                mov.b   #200,r0h
                sub.b   r0h,r0l
serin_no_rollover:
                mov.b   r0l,@gps_heading_dd
                rts		
;
; ---------------------------------------------------------
;
; Now parse the $GPRMC string for heading and speed
;
;	parce $GPRMC and ignore any other strings
;$GPRMC,214151.000,A,3742.0840,N,12152.0980,W,64.13,90.76,280112,,*19
;					      SSSSS BBBBB
;$GPRMC,215522.000,A,3746.7552,N,12150.0657,W,41.50,288.75,280112,,*2A
;					      SSSSS BBBBBB
;$GPRMC,221500.000,A,3740.7032,N,12155.2404,W,0.01,5.41,280112,,*1A
;					      SSSS BBBB
;Speed in Knots (just a little faster than mile/hr)
;	$GPRMC string, speed and bearing not the same length
;	Have to find $GPRMC and then count ','s to desired fields
;	Speed after 7th ','	read only intergers and not 1/10
;	Bearing after 8th ','	read only intergers and not 1/10
;	checksum who cares
;	String ends with CR LF                
;
; ---------------------------------------------------------
p_serial_output2:
;
;	Check Opt -G if False send Bearing info in 1 byte DD
;	If the UART is ready to send
;	Send Q when it changes.  
;	Format h'fQ. The value of DD will not reach h'f0
;		Note DD = Doppler Degrees 0 to 199
;		          Hardware limit
;     ELSE
;	Echo GPS string + decimal Bearing and Q

;       Only going to send characters if there any to send
;       and the output uart is ready.
;
;     If send DD-Q
;
;	Qcount = 0
;	Yes	No
;	|	|
;	|	|
;	|	Q = LastQ ----
;	|	No	      Yes
;	| 	|		|
;	|	| 		|
;	|    Qcount = 1 	|
;	|    No	      Yes	|
;	|    |		|	|
;	|    |		|	|
;	Send Q		| ______/
;	|	  	|/
;	Qcount=0	Send DD
; 	\______________ |
;		       \|
;			inc Qcount
;
		mov.b	@GPS_echo_flag,r1l
		bne	p_serial_output2_G
		btst    #tx_ready_bit,@s1_serial_status_reg
                beq     p_serial_out2_exit
;							; Start of Q or DD
;							; send logic                
                mov.b	@Q_count,r2h
                beq	p_serial_output2_Q		; Yes: Send Q
                mov.b	@last_sent_Q,r1h
                mov.b	@doppler_qual_0T9,r1l
                cmp.b	r1l,r1h				; same?
                beq	p_serial_output2_Bearing	; Yes
                cmp.b	#1,r2h				; Qcount = 1?
                beq	p_serial_output2_Bearing
                
p_serial_output2_Q:
                mov.b	#0,r2h
                mov.b	r1l,@last_sent_Q
                or	#h'0f0,r1l			; Format h'FQ
                bra	p_serial_output2_Byte
;
p_serial_output2_Bearing:
                mov.b	@qsync_bearing,r1l		; DD Bearing
p_serial_output2_Byte:                
                mov.b   r1l,@s1_tx_data			; Send it
;
;       Take care of ready bit and xmitter data empty
;
                bclr    #tx_ready_bit,@s1_serial_status_reg
                inc	r2h
                mov.b	r2h,@Q_count
                rts
;		
p_serial_output2_G

                mov.w   @output_buffer2_in_ptr,r1
                mov.w   @output_buffer2_out_ptr,r0
                cmp.w   r0,r1
                bne     p_serial_out2_send_a_char
                rts

p_serial_out2_send_a_char:

                btst    #tx_ready_bit,@s1_serial_status_reg
                beq     p_serial_out2_exit

;       Have a character, the UART is ready, let's do it.

                mov.b   @r0,R1l
                adds    #1,r0			; inc ptr
                mov.b   r1l,@s1_tx_data		; Send it

;       Take care of ready bit and xmitter data empty

                bclr    #tx_ready_bit,@s1_serial_status_reg

;       Check for the end of buffer 

                mov.w   #output_buffer2_end,r1
                cmp.w   r0,r1
                bne     p_serial_out2_save
                mov.w   #output_buffer2,r0
;
p_serial_out2_save:
                mov.w   r0,@output_buffer2_out_ptr
;
p_serial_out2_exit:
                rts
;
; ---------------------------------------------------------
;
;p_buttin:
;       What we want to do:
;
;       debounce the keys
;               read for any  button down then set flag & exit
;               if flag (counter? ) set get button number
;
;       Set timer for posible hold down second function
;       If time expires add 8 to button number
;
;       Look for button up
;               clear timer
;               check for calabrate mode for buttons 1 to 4 XXXXXXX
;               exicute
;
;       Reset debounce flag on exit
;
p_buttin:
                mov.b   #0,R0h
                mov.b   r0h,@port3_dr           ; set data bus to Zero
                mov.b   @hdw_button_bit,r0L     ; get bit to test
                btst    r0L,@button_in_dr       ; read buttons
                bne     but_up
                                                ; some button down

                mov.b   @but_debounce_flag,R0h
                beq     but_down_debounce_st
                dec	r0h
                mov.b   r0h,@but_debounce_flag
                beq     but_debounced
                rts

but_down_debounce_st:
                mov.b   @but_number_stor,R0h    ; Do we have a #
                bne     but_down_debounce_exit  ; Yes
                mov.b   #120,R0h                ; set counter scan
                mov.b   R0h,@but_debounce_flag  ; when zero
but_down_debounce_exit:
                rts

but_debounced:
                mov.b   @but_number_stor,R0h
                beq     but_scan                ; if no button #
                rts

but_scan:
                mov.w   #BUT_2ND_FUNCTION_TIME,R0
                mov.w   R0,@rt_msec_but_2nd     ; 1000 ms

;       if timer expires before but_up & but_number_stor not = 0
;       add 8 to but_number_stor

;       Scan for button, all eight
                mov.b   #h'fe,r1h
                mov.b   #1,r1L
but_scan_loop:
                mov.b   r1h,@port3_dr          ; bit 4 rev 0
                mov.b   @hdw_button_bit,r0L     ; bit 6 rev 1
                btst    r0L,@button_in_dr
                bne     but_scan_next
                mov.b   R1L,@but_number_stor

                rts
but_scan_next:
                inc     R1L
;       keep track of which button
;       Started with 1111 1110 ends with 0000 0000 if no button found
                shll    r1h
                bcs     but_scan_loop
;       R1h now zero

                rts                             ; button not found?

but_up:
		mov.w   #0,R0
                mov.b   r0l,@but_debounce_flag
                                   		; turn off timer
                mov.w   R0,@rt_msec_but_2nd
                mov.b   @but_number_stor,R1L    ; Do we have a #

                bne     but_exicute             ; Yes
                rts
but_exicute:

;       Find get function code from button function table.
                mov.b   #0,r1h
                subs    #1,r1
;       Button function # now in R1 and indexed to zero for button 1
                mov.w   #button_1_function,r2   ; First entry in RAM button table
                add.w   r1,r2
                mov.b   @r2,r0l

;       Get funtion # from table.
;       Allows user asignment of functions to any key

;       fall thru to buttin_execute
buttin_execute:

;       Play button press feedback, if turned on.

                mov.b   @ctrl_byte_Button_click,r1L
                beq     buttin_no_key_click
                mov.w   #h'e71f,r1
                mov.w   r1,@sound_queue
                mov.b   #1,r1l
                mov.b   r1l,@sound_length
                mov.b   #0,r1l
                mov.b   r1l,@sound_position
                mov.b   #PROCESS_RUN,r1l
                mov.b   r1l,@ps_sound_driver

buttin_no_key_click:

;       Find the button function entry (ID in r0l)
                mov.w   #button_table,r1

buttin_search:
                mov.w   @r1+,r2         ; inc R1 by 2
                cmp.b   r0l,r2l
                beq     buttin_call
                cmp.b   #h'ff,r2l
                beq     buttin_done
;       Not found, skip the rest of the record.
                mov.w   #10,r2          ; inc R1 by 10
                add.w   r2,r1           ; point to next
                bra     buttin_search

buttin_call:

;       Now is time to execute the button function

                mov.w   @r1,r0
                jsr     @r0

buttin_done:
;       Clear the button register, this is so we can check easily
;       on the entry point of the button process.
                mov.w   #0,r0
                mov.b   r0l,@but_debounce_flag
                mov.b   r0l,@but_number_stor
                rts


; ---------------------------------------------------------

;       Led Display, in a fancy fashion, impress your friends,
;       they will want to get one of these cool dopplers too!
;       The process does nothing useful. It does have the side effect of
;       talking straight to the LED matrix. It by passes the LED_DRIVER.
;       The led_driver should be stopped before this process runs.

p_attractor:
;
;       Output the leds

                mov.b   @led_id,r1l

;       Calculate which quadrant...

                mov.b   @led_quadrant,r2l
                adds    #1,r2
                mov.b   r2l,@led_quadrant
                and     #h'03,r2l
;       Q1
                cmp.b   #0,r2l
                beq     p_attractor_output_led_value
;       Q2
                cmp.b   #2,r2l
                bne     p_attractor_try_q3
                mov.b   #25,r3l
                sub.b   r1l,r3l
                mov.b   r3l,r1l
                bra     p_attractor_output_led_value
;       Q3
p_attractor_try_q3:
                cmp.b   #3,r2l
                bne     p_attractor_try_q4
                mov.b   #25,r3l
                add.b   r3l,r1l
                bra     p_attractor_output_led_value
;       Q4
p_attractor_try_q4:
                mov.b   #50,r3l
                sub.b   r1l,r3l
                mov.b   #50,r2l
                cmp.b   r2l,r3l
                bne     p_attractor_Q4_out
                mov.b   #0,r1l
                bra     p_attractor_output_led_value

p_attractor_Q4_out:
                mov.b   r3l,r1l

p_attractor_output_led_value:
                mov.b   r1l,@led_port
;       Do this when the slow timer decrements to zero
                mov.w   @rt_msec_attractor,r0
                beq     p_attractor_incr
                rts

p_attractor_incr:
                mov.w   #led_delay_initlower,r0
                mov.w   r0,@led_delay

                mov.b   @led_id,r1l

;       if( led_dir == 0 ) then decr else incr

                mov.b   @led_dir,r1h
                beq     p_attractor_decr

                adds    #1,r1
                cmp.b   #12,r1l
                bne     p_attractor_done
                mov.b   #0,r1h
                mov.b   r1h,@led_dir
                bra     p_attractor_done

p_attractor_decr:
                subs    #1,r1
                cmp.b   #h'ff,r1l
                bne     p_attractor_done
                mov.b   #1,r1l
                mov.b   #1,r1h
                mov.b   r1h,@led_dir

p_attractor_done:
                mov.b   r1l,@led_id

                mov.w   #ATTRACT_INCR_TIMER,r0
                mov.w   r0,@rt_msec_attractor
                rts

; ---------------------------------------------------------

;       Doppler LED display for doppler info. This process
;       decides what the LED ring should display. It will look at mode
;       words and do the right thing. The led ring can display:
;               relative doppler bearing
;               absolute doppler bearing
;		of any filter


p_led_ring_display:

                mov.b   #PROCESS_RUN,r0l
                mov.b   r0l,@ps_led_ring_display

;       If user wants the display held, do not do anything.

                mov.b   @ctrl_byte_stop_leds,r0L
                beq     p_led_ring_no_exit
                rts
p_led_ring_no_exit:
                mov.b   @ctrl_byte_hold,r0L
                bne     p_led_ring_hold_it
                mov.b   @ctrl_byte_PTT,r0L
                beq     p_led_ring_do_display
p_led_ring_hold_it:
                
                jmp     p_led_ring_done

p_led_ring_do_display:
;
;	Move filter-Absoulte selection to here
;	If filter = A then display all Filters in rotating order
;	Keep in Abslute-Relitive mode
;	Do the same thing for the pointer
;	Need a RAM locations for LED-Pointer to keep track of witch filter to use

		mov.w	@data_4_leds,r0		; get address to data
                mov.w   @r0,r1			; get data

                jsr     util_set_dop_deg_to_led

p_led_ring_done:
;----------------------------------------------------------

;       All done with seven seg display

; ---------------------------------------------------------
;       This utility is used in the serial in process
;       and the snoop process to determine if we need
;       to do a snoop print.

util_query_do_aprs_snoop:

util_query_simple:
               mov.b   @snooper_qlevel,r0h
               mov.b   @doppler_qual_0T9,r0l
               cmp.b   r0h,r0l
               bhs     util_query_do_true

util_query_do_false:
               mov.b   #0,r0l          ; flag false
               rts

util_query_do_true:
               mov.b   #1,r0l          ; flag true
               rts

;----------------------------------------------------------
;
;;       Print out a degree snoop, with the calculated quality value.
;
;;       Display Latest position value
;
;;       If we are currently doing a pass through operation,
;;       Just queue up the bearing request.
;
;p_aprs_snooper:
;p_snooper_check_write:
;                jsr     util_query_do_aprs_snoop
;                beq     p_snooper_request_only_gps
;
;                mov.b   #1,r1L
;                mov.b   r1L,@ctrl_byte_Snoop_pending
;
;p_snooper_request_only_gps:
;
;
;                mov.b   #1,r2L
;                mov.b   r2L,@GPS_capture_flag_SNOOP_PENDING
;                mov.b   @GPS_capture_flag,r2L
;                bne     p_snooper_exit
;
;;       Nothing important happening on the serial port,
;;       Spit out the bearing information.
;
;p_snooper_really_write:
;;       The snoop_pending bits must be set
;;       in order for this routine to work.
;                jsr     p_util_snooper_write
;
;p_snooper_exit:
;                mov.w   @snooper_constant,r0
;                mov.w   r0,@rt_sec_snooper
;                mov.b   #PROCESS_SLEEP,r0l
;                mov.b   r0l,@ps_aprs_snooper
;                rts
;
;;       This routine will write out:
;;               %RRR.R/Q%AAA.A
;;               $GPS capture string (if valid)
;
;p_util_snooper_write:
;
;                mov.b   @ctrl_byte_BEARING_FORCE_SNOOP,r1L
;                bne     p_util_snooper_write_it
;                mov.b   @ctrl_byte_Snoop_pending,r0L
;                beq     p_util_snooper_write_check_gps
;
;                jsr     util_query_do_aprs_snoop
;                beq     p_util_snooper_write_check_gps
;                mov.b   @doppler_qual_0T9,r1l
;                mov.b   @snooper_qlevel,r0l
;                cmp.b	r0l,r1l
;                bhs	p_util_snooper_write_it
;;????
;;????                blt     p_util_snooper_write_check_gps
;
;p_util_snooper_write_it:
;                jsr     util_write_bearing
;                mov.w   #eol_str,r1
;                jsr     @@write_buffered_str
;
;;       Write GPS if it is valid
;p_util_snooper_write_check_gps:
;                mov.w   @rt_sec_gps,r0
;                beq     p_util_snooper_exit
;
;                mov.b   @GPS_capture_flag_SNOOP_PENDING,r0L
;                beq     p_util_snooper_exit
;                mov.w   #gps_valid_capture,r1
;                mov.b   @r1,r0l
;                beq     p_util_snooper_exit
;                mov.w   #gps_valid_capture,r1
;                jsr     @@write_buffered_str
;                mov.b   #LF,r1l
;                jsr     @@write_buffered_char
;p_util_snooper_exit:
;
;
;                mov.b   #0,r0H
;                mov.b   r0H,@ctrl_byte_Snoop_pending
;                mov.b   r0H,@ctrl_byte_BEARING_FORCE_SNOOP
;                mov.b   r0H,@GPS_capture_flag_SNOOP_PENDING
;                mov.b   r0H,@ctrl_byte_APRS_LIMIT
;
;
;;       Clean up check, if the GPS sentence is stale
;;       and we are in GPS mode, this means that the
;;       GPS stream was stopped. Clear these bits.
;
;                mov.b   @GPS_capture_flag,r0L
;                beq     p_util_write_bearing_final_exit
;
;                mov.w   @rt_sec_gps,r0
;                bne     p_util_write_bearing_final_exit
;                mov.b   #0,r0L
;                mov.b   r0L,@GPS_capture_flag
;
;p_util_write_bearing_final_exit:
;                rts

; -----------------------------------------------------------------

;       Take a generic quality value from -ff80 to +007f
;       and map it to 0 to 9.
;       The quality value you want mapped to r1.

;       If the result is less than 0, return 0.
;	Input = doppler_qual_raw
;       The result is returned in r0
QUALTY_9:	.equ	87
util_map_qual_to_9:

		mov.w   @doppler_qual_raw,r1
		bmi	map_qual_0
		mov.b	#0,r0h
		mov.b	#9,r0l	
		cmp	#QUALTY_9,r1l
		bhs	map_qual_exit
		mov.b	#8,r0l
		cmp	#QUALTY_9/10 * 8,r1l
		bhs	map_qual_exit
		mov.b	#7,r0l
		cmp	#QUALTY_9/10 * 7,r1l
		bhs	map_qual_exit
		mov.b	#6,r0l
		cmp	#QUALTY_9/10 * 6,r1l
		bhs	map_qual_exit
		mov.b	#5,r0l
		cmp	#QUALTY_9/10 * 5,r1l
		bhs	map_qual_exit
		mov.b	#4,r0l
		cmp	#QUALTY_9/10 * 4,r1l
		bhs	map_qual_exit
		mov.b	#3,r0l
		cmp	#QUALTY_9/10 * 3,r1l
		bhs	map_qual_exit
		mov.b	#2,r0l
		cmp	#QUALTY_9/10 * 2,r1l
		bhs	map_qual_exit
		mov.b	#1,r0l
		cmp	#6,r1l
		bhs	map_qual_exit
map_qual_0:		
		mov.b	#0,r0l
map_qual_exit:
		mov.b	r0l,@doppler_qual_0T9
                rts
;
util_map_qual_to_9_minus:
                mov.w   #0,r0
                rts
;
; --------------------------------------------------------------

util_write_calibrations:

                push    r1
                push    r2

                mov.w   #str_calibration_header,r1
                jsr     @@write_buffered_str
; Added 2011-12-30
                mov.b   @current_config,r0l                
                jsr     get_config_ptr
                adds	#2,r0
                mov.b	#10,r2l
                push	r0
cal_loop:
		pop	r0                
                mov.b	@r0+,r1l
                push	r0
                mov.b   #0,r1h                              
                jsr     @@write_dec_word                                   
                mov.w   #bstr_separator,r1
                jsr     @@write_buffered_str;
                dec	r2l
                bne	Cal_loop
                pop	r0
;
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
                pop     r2
                pop     r1
                rts

; ---------------------------------------------------------
;
write_current_config:
                mov.w   #str_current_config,r1
                jsr     @@write_buffered_str		
		mov.b   @current_config,r1l
		jsr	write_0toF
		
; Fall thru to util_write_antenna_config
;----------------------------------------------------------
util_write_antenna_config:
                push    r1
                

                mov.w   #str_antenna_is,r1
                jsr     @@write_buffered_str

                jsr     util_get_antenna_config
                and     #h'f0,r0l
                shlr    r0l
                shlr    r0l
                shlr    r0l
                shlr    r0l
                mov.b   r0l,r1l
                jsr     write_0toF
                jsr     util_get_antenna_config
                and     #h'0f,r0l
                bne     util_write_antenna_high
                mov.w   #str_antenna_sw_lo,r1
                bra     util_write_antenna_level
util_write_antenna_high:
                mov.w   #str_antenna_sw_hi,r1
util_write_antenna_level:
                jsr     @@writeln_buffered_str

                pop     r1
                rts

; ---------------------------------------------------------
;	Doppler degree (0-199)passed in r1 convert to 4 ascii (0-360)
;	ret with ascii in r0l =  100s
;			  r0h =   10s
;			  r1l =    1s
;			  r1h = 1/10s
;
degrees_convert:
		push	r2
                mov.b   #18,r0l  		; doppler counts * 1.8
                mulxu   r0l,r1                  ; now have fixed pt degrees
                				; but 10 x of correct value
                				; 102 dop deg = 1836 in binary

;       Split value to hundreds-tens
;       and ones-tenths.
                mov.b   #100,r0l
                divxu   r0l,r1			; r1l = deg 100s and 10s   in binary (18)
                				; r1h = deg 1s   and 1/10s in binary (36)
                mov.w   r1,r0
		mov.b	r1h,r2l			; save 1s and 1/10s
;       Split hundreds and tens
                				; deg 100s and 10s
                mov.b   #0,r1h
                mov.b   #10,r2h
                divxu   r2h,r1			; r1l = 100s  r1h = 10s binary
                add.b   #'0',r1l
		add.b   #'0',r1h		; now ascii

;
                mov.b   #0,r0h
                mov.b	r2l,r0l
                mov.b   #10,r2l
                divxu   r2l,r0			; r0l = 1s  r0h = 1/10s binary

                add.b   #'0',r0l
		add.b   #'0',r0h		; now ascii		
		pop 	r2
		rts

;
;----------------------------------------------------------
;       Doppler degree (0-199)passed in r1, write real degrees to serial 0.
;
degrees_write_s0:
;
		jsr	degrees_convert
		jsr     @@write_buffered_char	; (r1l)
		mov.b	r1h,r1l
		jsr     @@write_buffered_char	; (r1l)
		mov.b	r0l,r1l
		jsr     @@write_buffered_char	; (r1l)
		mov.b	#'.',r1l
		jsr     @@write_buffered_char	; (r1l)
		mov.b	r0h,r1l
		jmp     @@write_buffered_char	; (r1l)
;
; -------------------------------------------------------------------------
;
;----------------------------------------------------------
;       Doppler degree (0-199)passed in r1, write real degrees to serial 0.
;
degrees_write_s1:
;
		jsr	degrees_convert
		jsr     write_buffered_char2	; (r1l)
		mov.b	r1h,r1l
		jsr     write_buffered_char2	; (r1l)
		mov.b	r0l,r1l
		jsr     write_buffered_char2	; (r1l)
		mov.b	#'.',r1l
		jsr     write_buffered_char2	; (r1l)
		mov.b	r0h,r1l
		jmp     write_buffered_char2	; (r1l)
;
; -------------------------------------------------------------------------
;
util_write_bearing:

;       This routine will write out:
;               %RRR.R/Q%
;       Where
;               RRR.R is a relitive bearing in degrees
;               Q     is the quality level 0 to 9
;
                mov.b   #  '%'  ,r1l
                jsr     @@write_buffered_char

                mov.w   @filt_0_output,r1     ; get  data
                jsr     degrees_write_s0

                mov.b   #  '/'  ,r1l
                jsr     @@write_buffered_char
                mov.b	@doppler_qual_0T9,r1l
                or	#'0',r1l
                jmp     @@write_buffered_char

;----------------------------------------------------------???                
;
util_write_check_compass:

;		mov.b	@GPS_capture_flag_compass_avail,r1L
;		beq	util_write_no_compass
util_write_have_compass:
		mov.b	#  '%'  ,r1l
		jsr	@@write_buffered_char
                mov.b   @gps_heading_dd,r0L
                mov.b   r0l,r1l
	        jsr     degrees_write_s0		
;
util_write_no_compass:
		rts
;		
;
; ---------------------------------------------------------

;       Monitor the output of the bandpass filter to try and
;       determine the quality of the doppler signal.
;       This routine continually services the A/D converters.

;       Gather channel 0 (the fundamental),
;       when complete take the doppler value.
;       Start channel 1 converting when 0 is complete.
;       When channel 1 is complete, restart channel 0.
;	every 2 mS
;       KN6FW has kindly rectified and filtered the signal
;
p_analog:
                mov.b   @analog_csr,r0l
                btst    #ANALOG_FINISH_BIT7,r0l
                bne	p_analog1
                jmp     p_analog_done
p_analog1:                			
                and     #h'03,r0l			; chan ? 0 = chan 0
                bne     p_analog_check_channel_1
;
;       Fundamental strength
p_analog_check_channel_0:

                push	r2
                mov.b	@doppler_qual_fundx,r0l
                inc	r0l
                cmp.b	#4,r0l
                bls	no_adj_an0
                mov.b	#0,r0l
no_adj_an0:
		mov.b	r0l,@doppler_qual_fundx
		shal	r0l
		mov.w	#doppler_qual_fund1,r1
		mov.b	#0,r0h
		add.w	r0,r1
		mov.b   @analog_channel_port_0_4,r0l	; read conversion
		mov.w	r0,@r1

		mov.w	#doppler_qual_fund1,r1
		mov.w	@r1,r0
		add.w	r0,r2				; 1 average sum r2
		adds	#2,r1
		mov.w	@r1,r0
		add.w	r0,r2				; 2 average sum r2
		adds	#2,r1
		mov.w	@r1,r0
		add.w	r0,r2				; 3 average sum r2
		adds	#2,r1
		mov.w	@r1,r0
		add.w	r2,r0				; 4 average sum r2
		shlr	r0h				; div by 2
		rotxr	r0l
		shlr	r0h				; div by 2
		rotxr	r0l						                
                mov.b   r0l,@doppler_qual_fund		; store fun
                
                mov.b   #ANALOG_START_1,r0l
                mov.b   r0l,@analog_csr
                pop	r2   
                rts
;
;       2nd harmonic strength
p_analog_check_channel_1:
                cmp.b   #1,r0l				; chan 1?
                bne     p_analog_check_channel_2
                mov.b   @analog_channel_port_1_5,r0l
                mov.b   r0l,@doppler_qual_2nd		; store 2nd
                mov.b   #ANALOG_START_2,r0l
                mov.b   r0l,@analog_csr
;
;       Calculate the difference between fundamental and
;       The second harmonic. Values GT 0 are good, and get
;       a bar graph. Values less than zero get no bar.
                mov.b   @doppler_qual_fund,r0l
                mov.b   #0,r0h
                mov.b   @doppler_qual_2nd,r1l
                mov.b   #0,r1h
                sub.w   r0,r1				; fun - 2nd
                mov.w   r1,@doppler_qual_raw
                jsr	util_map_qual_to_9
                jsr     p_analog_display_qbars

;       Compass channels.
;       The compass channels are retrieved and stored in RAW form.
;       Routines that want to use this must process the values to
;       calibrated form.
;       This is done is the routine that "get_compass_value".

p_analog_check_channel_2:
                cmp.b   #2,r0l
                bne     p_analog_check_channel_3
                mov.b   @analog_channel_port_2_6,r0l
                mov.b   r0l,@analog_channel_2_data
                mov.b   #ANALOG_START_3,r0l
                mov.b   r0l,@analog_csr
                bra     p_analog_done

p_analog_check_channel_3:
                cmp.b   #3,r0l
                bne     p_analog_done
                mov.b   @analog_channel_port_3_7,r0l
                mov.b   r0l,@analog_channel_3_data

p_analog_check_channel_3_done:
                mov.b   #ANALOG_START_0,r0l
                mov.b   r0l,@analog_csr

p_analog_done:
                rts

;       Utility method to set the qbar display, called from panalog.

p_analog_display_qbars:
		mov.b	@doppler_qual_0T9,r0l
		bne	test_bars_1
                mov.b   #SEG_PAT_DOT,r1l
                bra     p_analog_set_qbar
test_bars_1:
		cmp.b	#3,r0l
		bhi	test_bars_2
                mov.b   #SEG_PAT_BAr1,r1l
                bra     p_analog_set_qbar
test_bars_2:
		cmp.b	#6,r0l
		bhi	bars_3
                mov.b   #SEG_PAT_BAr2,r1l
                bra     p_analog_set_qbar
bars_3:
                mov.b   #SEG_PAT_BAr3,r1l
p_analog_set_qbar:
                mov.b   r1l,@led_7_qbar
                rts

; ---------------------------------------------------------

;       This process is the equivalent to the led_ring display.
;       We can use it to determine what parameters will be
;       on the pointer.
;       One possible use would be to switch between doppler
;       and compass values.

;pointer display location

p_dial_out:

;       If user wants the display held, do not do anything.

                mov.b   @ctrl_byte_PTT,r0L
                bne     p_dial_out_exit
                mov.b   @ctrl_byte_hold,r0L
                bne     p_dial_out_exit


                mov.w   @data_4_ptr,r0          ; get address to data
                mov.w   @r0,r0                  ; get data
;                add.w	r0,r0			; make it 2x
;
;	multiply by two for the stepper. Make it 0 to 398.
;
;	Average 2 readings and forget the div by 2
;	If the differance of the 2 values is GT 100
;	and sum of the 2 is GT 200 subtract 200
;	if sum is LT 200 add 200
;
;
                mov.w	@pointer_target2,r1	; old point
                sub.w	r0,r1
                bpl	ans_positive_dif
                neg	r1l
ans_positive_dif:
		cmp.b	#100,r1l
		blo	dif_LT_100
		beq	dif_EQ_100		; don't know what to do
						; 0 & 100 = 50 or 150?
dif_GT_100:
		mov.w	@pointer_target2,r1	; old point
		add.w	r0,r1			; new data + old data
		mov.w	r0,@pointer_target2	; save next old data
		mov.w	#200,r0
		cmp.w	r0,r1
		bhs	GT_200
LT_200:
		add.w	r0,r1
		mov.w   r1,@pointer_target
		rts
GT_200:	sub.w	r0,r1
		mov.w   r1,@pointer_target
		rts
;
dif_LT_100:
		mov.w	@pointer_target2,r1	; old point
		mov.w	r0,@pointer_target2	; save next old data
		add.w	r1,r0
dif_EQ_100:
p_dial_out_exit:		
                mov.w   r0,@pointer_target
                
                rts

; ---------------------------------------------------------
;
;	Input 0-199. from @data_4_ptr,r0 -> @r0,r0
;	Save current position
;	Timer for stepper motor to settle.
;	Step cw or ccw one step or do nothing.
;	Find shortest path from current position to next position.
;	Calabrate with over radiator input. Only in cw direction.

;       This is the low level driver for the stepper motor.
;       Because it is a driver, the health of the doppler is
;       dependent upon it.
;       This process should never be turned off
;       (except by doppler software).

;       This math is tricky in that we are attempting to
;       determine the direction to step in.
;       Since we would like to step in the shortest
;       direction, we figure that out.
;       We see how far it would take to get
;       to the target direction in both directions.
;       The pointer is stepped in the direction that would
;       result in the shortest number of steps.
;	Input from @pointer_target DD times 2 or 0 to 398

p_stepper_driver:
                mov.w   @rt_msec_stepper,r0
                beq     stepper_reset_timer
;       Should not be running when the timer isn't empty...
                mov.b   #PROCESS_SLEEP,r0l
                mov.b   r0l,@ps_stepper_driver
                rts

;       OK, we can move now,
;       the motor has had enough time to settle out.

stepper_reset_timer:
;       Reset the wait timer
                mov.w   @pointer_delay,r0
                mov.w   r0,@rt_msec_stepper
;
                mov.w   @pointer_target,r1	; input info 0 to 398
                mov.w   @pointer_location,r2	; what the stepper "thinks"
;
                cmp.w   r1,r2			; Same do nothing
                bne     stepper_find_direction
                rts
;
stepper_find_direction:
;
;       1/2 the ptr circle has this many,counts.
                mov.w   #200,r3
                jsr     util_calc_dir_vector	; r0h  CW = 0 | CCW = 1
		mov.b	r0h,r0h
;
; Now have direction to step lets do the step
; if CW and the zero bit goes low set @pointer_location to 0
; need to keep @pointer_location current so add or sub 1
; correct of ends if it's 0 and sub 1, make it 399
; if it's 399 and add 1, make it 0
;		
		beq	step_cw
step_ccw:
		mov.w   @pointer_location,r2
		bne     stepper_subtract_one
;       underflow, set to max (360 degrees == 399 counts)
                mov.w   #399,r2
                bra     stepper_save_location
;
stepper_subtract_one:
                subs    #1,r2

stepper_save_location:
;       r2 contains the new (incremented) location
                mov.w   r2,@pointer_location
; do the ccw step *****************************************
		mov.b	#CCW,r1l		; step
		jsr	stepper_single_step
stepper_return:
                rts
		
step_cw:
		mov.w   @pointer_location,r2
		adds	#1,r2
		mov.w	#400,r1
		cmp.w	r1,r2
		bne	cw_location_ok
		mov.w	#0,r2                
cw_location_ok:
		mov.w	r2,@pointer_location
; do the cw setp ******************************************
		mov.b	#CW,r1l			; step
;		jsr	stepper_single_step
;		rts
; Fall thru to stepper_single_step
;
; ---------------------------------------------------------

;       Pass in r1l either CW = 0 | CCW = 1, and we will step the motor.
;       This routine is very low level, and deals with the pointer
;       state machine and quadrature signals. This routine is only
;       called from the stepper motor driver. NOT TRUE

;       If r1h is TRUE, turn off the lights,
;       otherwise leave them on.

stepper_single_step:
;                mov.b   r1h,@temporary		; Error not back-lite info
;
                cmp.b   #CW,r1l
                bne     stepper_single_ccw
                mov.b	#0,r1h			; turn off cal, changed dir
                mov.b	r1h,@zero_info_reed_closed
                mov.w   @pointer_state,r1	; state machine @ data
                adds    #2,r1			; now at forward link
                bra     stepper_single_do_it

stepper_single_ccw:
                btst	#2,@port_9		; 0 = not at zero
                beq	its_not_zero
                mov.b	#1,r1h
                mov.b	r1h,@zero_info_reed_closed
its_not_zero:                
                mov.b	r1l,@zero_info_direction
                mov.w   @pointer_state,r1
                adds    #2,r1			; now at forward link
                adds    #2,r1			; Backward link

stepper_single_do_it:
;
;       Access thru the ForwardLINK or BackwardLINK
;       Get next state pointer
;
                mov.w   @r1,r0			; r1 pointing to address
                				; of next step data
						;                
						; Remember where we are 
						; in the state table.
						; get pointer right
                mov.w   r0,@pointer_state	; save state
;                
;       Get the bit values
;
                mov.w   @r0,r1			; now have data 
                				; to move stepper
;       Check hardware version to use the correct signals

                mov.b   @hardware_version,r0l	; rev 0 = 0
                beq     stepper_single_doit
                mov.b   r1h,r1l			; now have data 
                				; to move stepper in r1l
;       Send the value to the stepper motor

stepper_single_doit:

        %IF    DEVELOP_ASM
;       For development.
;	bit  0   ffc1	nc
;	bit  1   ffc1	motor 2
;	bit  2   ffc1	input
;	bit  3   7ff7	back-lite	; needs to be high	
;	bit  4   7ff7	motor 4
;	bit  5   7ff7	motor 3
;	bit  6   7ff7	nc
;	bit  7   7ff7	motor 1
;
                mov.b   #h'06,r1h
                and     r1l,r1h         ; r1h = port ffc1 data port
                and     #h'0f8,r1l      ; r1L = port 7ff7 data emulator
                bset	#3,r1l		; turn on back-lite always
                mov.b   r1h,@h'ffc1
                mov.b   r1L,@h'7ff7
;
        %ELSE
        	bset	#3,r1l		; turn on back-lite always
                mov.b  r1l,@h'ffc1
	%ENDIF
						; settle time dummy                 
                 mov.b	@zero_info_direction,r1l	
                 				; CW = 0 CCW =1
                 beq	exit_going_cw
                 mov.b	@zero_info_reed_closed,r1l			 
                 				; closed = 1
                 beq	zero_not
                 				; got here if magnet
                 				; over reed, port_9-2 = 1
                 btst	#2,@port_9
                 bne	zero_not		; still a 1
                 				; went to 0
;
                 mov.w	#0,r0
                 mov.b	r0l,@zero_info_reed_closed
                 				; no longer closed
                 mov.w	r0,@pointer_location
zero_not:
exit_going_cw: 
		rts
;
; ---------------------------------------------------------
;
;	If ever you have to work on this routine.
;	Leave one time slot between LED ring display
;	Next time disable port to turn off all outputs
;	Next time DD 99 or 100 to front. It makes filters easier.
;	Layout with one led at 0 degrees.
;       This is another driver process and should never be disabled.
;       This driver will multiplex the LED matrix.
;       It is responsible for displaying the LED on the ring
;       (LED_PRIMARY) and walking through the state machine to
;       display the 7 segment display.

;       if( rt_msec_marquee == 0 )
;               if( led_7_marquee_idx >= MARQUEE_SIZE )
;                       led_7seg_pattern = current_qbar_pattern
;               else
;                       if( buffer[idx] == h'ff )
;                               led_7_seg_pattern == current_qbar_pattern
;                       else
;                               led_7_seg_pattern = pattern_table[buffer[idx]]
;                       idx++
;                       rt_msec_marquee = MARQUEE_TIME_VALUE

p_led_driver:
;       Dim mode
                mov.b   @ctrl_byte_Dim_LED,r0L
                beq     p_led_driver_no_dim
                mov.w   @rt_clock_msec,r0
                and     #h'03,r0l
                beq     p_led_driver_no_dim
;
;       Dim it
                mov.b   #LED_UNUSED_LOCATION,r0l
                mov.b   r0l,@led_port
                rts
;
p_led_driver_no_dim:

                mov.w   @rt_msec_marquee,r0
                bne     led_driver_show_7_seg
                mov.b   @led_7_marquee_idx,r2l
                mov.b   @led_7_marquee_length,r2h
                cmp.b   r2h,r2l
                blt     p_led_driver_get_next_character
p_led_driver_show_qbar:
;       The marquee is empty, or wants qbar
                mov.w   #MARQUEE_IDLE_TIME,r1
                mov.w   r1,@rt_msec_marquee

;       Remember that a qbar is being done.

                mov.b   #h'ff,r1l
                mov.b   r1l,@led_7_current_char
                mov.b   @led_7_qbar,r1l
                bra     p_led_driver_set_new_7seg_pattern

;       Have an active character to display

p_led_driver_get_next_character:
                mov.w   #led_7_marquee,r0
                mov.b   #0,r2h
                add.w   r2,r0
                mov.b   @r0,r1l

;       Grabbed the next character
;       remember what char is being done

                mov.b   r1l,@led_7_current_char

;       Marquee demands a qbar display if index == $ff

                cmp.b   #h'ff,r1l
                bne     p_led_driver_next_char_cont
                mov.b   @led_7_qbar,r1l

p_led_driver_next_char_cont:
                adds    #1,r2
                mov.b   r2l,@led_7_marquee_idx
                mov.w   #MARQUEE_TIME_VALUE,r2
                mov.w   r2,@rt_msec_marquee
p_led_driver_set_new_7seg_pattern:
                jsr     set_7seg_pattern

led_driver_show_7_seg:
                mov.b   @led_disp_primary_flag,r0l
                bne     p_led_driver_do_primary

                mov.w   @led_7seg_pattern,r2
                beq     p_led_driver_do_primary

;       Look up the segment value
led_driver_continue_7_seg:
                mov.b   @led_7_seg_idx,r1l
                mov.b   #0,r1h
                add.w   r1,r2
                mov.b   @r2,r0l
                beq     led_driver_7_segment_reset
                adds    #1,r1
                mov.b   r1l,@led_7_seg_idx
                bra     led_driver_done

;       Seem to be at the end of the segment list
;       recycle the count and just display primary

led_driver_7_segment_reset:
                mov.b   #0,r0h
                mov.b   r0h,@led_7_seg_idx

;       If the current character is an idle, update the pattern
;       Note that the qbar pattern is only updated AFTER displaying
;       all the elements. This prevents strange display artifacts.
;       This doesn't affect the display of the primary LED. This
;       still must happen.

                mov.b   @led_7_current_char,r0l
                cmp.b   #h'ff,r0l
                bne     p_led_driver_do_primary

;       It appears as though it is showing qbar, either idle or
;       on demand in the marquee.

                mov.b   @led_7_qbar,r1l
                jsr     set_7seg_pattern
;
p_led_driver_do_primary:
                mov.b   @led_disp_primary_flag,r0l
                bne     p_led_driver_do_secondary
                mov.b   @led_primary,r0l
                mov.b   #h'ff,r0h
                bra     p_led_driver_do_ring
p_led_driver_do_secondary:
                mov.b   #0,r0h
                mov.b   @led_secondary,r0l

p_led_driver_do_ring:
                mov.b   r0h,@led_disp_primary_flag

;       See if we need to blink the primary (high order bit set)

                btst    #7,r0l
                beq     led_driver_done

                mov.w   @led_blink_timer,r1
                and     #h'08,r1h
                bne     led_driver_done
                mov.b   #LED_UNUSED_LOCATION,r0l

led_driver_done:
                mov.b   @ctrl_byte_stop_leds,r1H
                beq     led_driver_no_stop
                rts

led_driver_no_stop:
                and     #h'7f,r0l                
                mov.b   r0l,@led_port

led_driver_abort:

;       Increment the blink counter
                mov.w   @led_blink_timer,r1
                adds    #1,r1
                mov.w   r1,@led_blink_timer

                rts

; ---------------------------------------------------------

;       Force a value to be displayed on the seven segement display.
;       This will reset the timer for full display time.
;       This is also used when the user changes states and
;       we want feedback.
;       Pattern in r1l (actually index into pattern table)

seg7_force_display:
                mov.w   #led_7_marquee,r0
                mov.b   r1l,@r0
                mov.b   #1,r0l
                mov.b   r0l,@led_7_marquee_length
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
                mov.w   #0,r0
                mov.w   r0,@rt_msec_marquee
                rts

;       Similar to the previous routine, but uses 2 patterns.
;       r1h / r1l are pattern index values into the table.

seg7_force_2display:
                mov.w   #led_7_marquee,r0
                mov.b   r1h,@r0
                adds    #1,r0
                mov.b   r1l,@r0

                mov.b   #2,r0l
                mov.b   r0l,@led_7_marquee_length
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
                mov.w   #0,r0
                mov.w   r0,@rt_msec_marquee
                rts

; ---------------------------------------------------------

; Toggle the 7 segment display between value 1 (r1h) and value
; value 2 (r1l). In between value 1 and value 2, display the idle
; pattern (quality bars).

; The trick with this routine is because it is called
;       continuously from within the loops, etc.
;       In order to operate properly, the routine detects if the
;       same toggle data is in the marquee.
;       If this routine would reset the same information,
;       then the marquee is not touched.
;       In that case, only the marquee display is restarted.

;       The display only is forced to toggle if nothing else
;       is being displayed.
;       This allows "seg7_force_diplay" to be able to provide
;       feedback while in a toggling display mode.

;        if( marquee_timer == 0) && (marquee_idx == marquee_length)
;        {
;               if( marquee_length == 4 )
;                       force_display()
;                else
;               {
;                       if (marquee[0] != r1h) || (marquee[1] != h'ff) ||
;                          (marquee[2] != r1l) && (marquee[3] != h'ff)
;                               force_display()
;                       else
;                       {
;                               if( (marquee_idx >= 4) && (marquee_timer == 0) )
;                                       marquee_idx = 4;  * restart marquee *
;                       }
;               }
;       }


seg7_toggle_display:
                push    r2
;       Only update if not busy
                mov.w   @rt_msec_marquee,r0
                bne     seg7_toggle_exit
                mov.b   @led_7_marquee_idx,r0h
                mov.b   @led_7_marquee_length,r0l
                cmp.b   r0h,r0l
                bne     seg7_toggle_exit

                cmp.b   #4,r0l
                bne     seg7_toggle_force
;       marquee[0] != r1h ?
                mov.b   @r0,r2l
                adds    #1,r0
                cmp.b   r1h,r2l
                bne     seg7_toggle_force
;       marquee[0] != h'ff ?
                mov.b   @r0,r2l         ; XXXXError     ?
                adds    #1,r0
                cmp.b   #h'ff,r2l
                bne     seg7_toggle_force
;       marquee[0] != r1l ?
                mov.b   @r0,r2l
                adds    #1,r0
                cmp.b   r1l,r2l
                bne     seg7_toggle_force
;       marquee[0] != r1h ?
                mov.b   @r0,r2l
                cmp.b   #h'ff,r2l
                bne     seg7_toggle_force
                mov.b   @led_7_marquee_idx,r0l
                cmp.b   #4,r0l
                bne     seg7_toggle_exit

seg7_toggle_force:
                mov.w   #led_7_marquee,r0
                mov.b   #h'ff,r2l
;       marquee[0] = r1h
                mov.b   r1h,@r0
                adds    #1,r0
;       marquee[1] = h'ff
                mov.b   r2l,@r0
                adds    #1,r0
;       marquee[2] = r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       marquee[3] = h'ff
                mov.b   r2l,@r0
                mov.b   #4,r0l
                mov.b   r0l,@led_7_marquee_length
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
seg7_toggle_exit:
                pop     r2
                rts

; ---------------------------------------------------------

;       Spin the rotation rates, pick up calibration values.

p_calibrate:

;       Have to be playing special games to calibrate...
;       During the calibration process the doppler
;       maintenece mode is set to "calibrate".
;       This indicates to this process that we are calibrating
;       and will let this process stop if weare not calibrating.

                mov.w   @maintenance_mode,r0
                btst    #MODE_MAINT_CALIBRATE_BV,r0l
                bne     p_calibrate_check_timer

;       Not really calibrating, and erroneously running,
;       just stop this process.

                mov.b   #PROCESS_STOPPED,r0l
                mov.b   r0l,@ps_calibrate
                rts

;       If we have waited long enough, grab the value and go.

p_calibrate_check_timer:
                mov.w   @calibration_timer,r0
                subs	#1,r0
                mov.w   r0,@calibration_timer	; set Z flag
                beq     p_calibrate_get_value                
                rts

p_calibrate_get_value:
                mov.b   #SEG_PAT_C,r1h
                mov.b   @current_rotation_rate,r1l
                jsr     seg7_force_2display

                mov.b   @current_rotation_rate,r1l	; Zero how
                bne     p_calibrate_print_regular

;       Print a leading EOL just to make it look better if
;       the user happened to do this via "execbtn bcal"

                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
p_calibrate_print_regular:
                mov.w   #str_calibrating_rate,r1
                jsr     @@write_buffered_str
                mov.b   @current_rotation_rate,r1l
                jsr     @@write_byte			; Display rot
                mov.b	#' ',r1l
                jsr	@@write_buffered_char
                mov.w   @raw_store,r0
                mov.b	r0l,r1l
                mov.b	#0,r1h
                jsr     @@write_dec_word		; Display true dop point
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
                mov.w	@raw_store,r0
                mov.b   @current_config,r0l
                jsr     get_config_ptr		; r0l in r0 out
                				; enabled - cal val not set
                                                ; 4 ant  - 1 active high   
                                                ; calibrate rot rate 0
		                                ; calibrate rot rate 1
                                                ; calibrate rot rate 2
                                                ; calibrate rot rate 3
                                                ; calibrate rot rate 4
                                                ; calibrate rot rate 5
                                                ; calibrate rot rate 6
                                                ; calibrate rot rate 7
                                                ; calibrate rot rate 8
                                                ; calibrate rot rate 9
                                                ; default rotation rate
                adds    #2,r0			; now points to rot 0

		mov.b   @current_rotation_rate,r1l
		mov.b	#0,r1h

                add.w   r0,r1
		mov.w	@raw_store,r2
;		inc	r2l
;		inc 	r2l
;		cmp.b	#200,r2l
;		bcs	cal_value_ok
;		add.b	#56,r2l
cal_value_ok:		
                mov.b   r2l,@r1
;
;       next rate (add one to r2, which is (rate-1))
                mov.b   @current_rotation_rate,r2l
                mov.b   #0,r2h
                inc     r2L
                cmp.b   #LAST_ROT + 1,r2l
                bne     p_calibrate_exit
;
;       Done calibrating all of the values
                mov.b   #0,r0l          	; flag false
                mov.b   r0l,@ps_calibrate
                mov.w   @maintenance_mode,r0
                bclr    #MODE_MAINT_CALIBRATE_BV,r0l
                mov.w   r0,@maintenance_mode



;       New rot rate
		mov.b	#5,r1l
                jsr     set_rotation_rate
                mov.b   r2h,r1l
                mov.b   #0,r1h
                jsr     seg7_force_display

;       Print prompt after calbrate
                mov.w   #str_prompt,r1
                jmp     @@write_buffered_str

p_calibrate_exit:
                mov.b   r2l,r1l
                jsr     set_rotation_rate
                mov.w   #CALIBRATION_WAIT_VALUE,r0
                mov.w   r0,@calibration_timer
                rts

; ---------------------------------------------------------

p_sound_driver:

;       To make this work:

;       The low  byte = tone ff being the lowest
;       The high byte = time if below 128 then 256X mS
;                            if 128 or higher then 128 = 127 mS
;                            and it goes lower.  Good for click.
;       Place the word in the "sound_queue".  It will hold 10.

;       Then set "sound_length" to the number of tones played.
;       Then set "sound_position" to zreo.

; ---------------------------------------------------------

                mov.b   @sound_position,r0l
                mov.b   @sound_length,r0h
                beq     p_sound_off
                cmp.b   r0l,r0h
                beq     p_sound_off
;p_sound_on:
;       Sound state contains the number of items in the queue
;       Sound position has which sound it to be played next.

                mov.w   #sound_queue,r1

;       Setup R0 to be an index value
;       Multiply index into queue by 2

                mov.b   #0,r0h
                shll    r0l
                add.w   r0,r1

                mov.w   @r1,r0
;       Get the sound queue entry
;       Low byte = frequency

                mov.b   r0l,@timer_1_const_A

;       Test the duration.
;       If it is negitive, then it is expressed as two complement of mSec.
;       Otherwise it is dur*256 mSec

;       1 to 127     = 256 mS to 32.5 Sec
;       h'ff to h'80 = 1 to 127 mS      Good for tick

                mov.b   r0h,r0l         ; Sets sign flag
                bpl     p_sound_set_timer

                mov.b   #0,r0h
                neg     r0l
                bra     p_sound_set_timer

p_sound_set_timer:
                mov.w   r0,@rt_msec_sounder

;       Set sound position for next iteration
                mov.b   @sound_position,r0l
                inc     r0L
                mov.b   r0l,@sound_position

                mov.b   #timer_1_tcr_val,r0l
                mov.b   r0l,@timer_1_tcr
                mov.b   #PROCESS_SLEEP,r0l
                bra     p_sound_driver_done

p_sound_off:
;       Turn off the sound
                mov.b   #0,r0l
                mov.b   r0l,@sound_length
                mov.b   r0l,@sound_position
                mov.b   #timer_1_tcr_off,r0l
                mov.b   r0l,@timer_1_tcr
                mov.b   #PROCESS_STOPPED,r0l
;
p_sound_driver_done:
                mov.b   r0l,@ps_sound_driver
                rts
; ---------------------------------------------------------

fence_process_end:

; ---------------------------------------------------------

fence_util_start:

; ---------------------------------------------------------

;       Set the pointer delay, based on pointer idx speed.
;       Pointer delay idx is passed in r1l.

util_set_pointer_delay:
                cmp.b   #0,r1l
                bne     util_set_pointer_delay_1
                mov.w   #POINTER_DELAY_SLOW,r0
                bra     util_set_pointer_delay_exit
util_set_pointer_delay_1:
                cmp.b   #1,r1l
                bne     util_set_pointer_delay_2
                mov.w   #POINTER_DELAY_MED,r0
                bra     util_set_pointer_delay_exit
util_set_pointer_delay_2:
                cmp.b   #2,r1l
                bne     util_set_pointer_delay_3
                mov.w   #POINTER_DELAY_FAST,r0
                bra     util_set_pointer_delay_exit
util_set_pointer_delay_3:
                cmp.b   #3,r1l
                bne     util_set_pointer_delay_4
                mov.w   #POINTER_DELAY_FASTER,r0
                bra     util_set_pointer_delay_exit
util_set_pointer_delay_4:
                cmp.b   #4,r1l
                bne     util_set_pointer_delay_default
                mov.w   #POINTER_DELAY_SCREAMER,r0
                bra     util_set_pointer_delay_exit
util_set_pointer_delay_default:
                mov.w   #POINTER_DELAY_INIT,r0
                mov.b   #POINTER_DELAY_IDX_INIT,r1l
util_set_pointer_delay_exit:
                mov.b   r1l,@pointer_delay_idx
                mov.w   r0,@pointer_delay
                rts
;
; ---------------------------------------------------------

;       Set the LED delay, based on current_LED_speed.
;       passed in r1l.

util_set_led_delay:
		mov.w   #LED_DELAY_SLOW,r0
		and	#h'03,r1l		; make 0 to 3
		beq	util_set_led_delay_exit ; it's 0
		mov.w   #LED_DELAY_MED,r0
		dec	r1l
		beq	util_set_led_delay_exit ; it's 1
		mov.w   #LED_DELAY_FAST,r0
		dec 	r1l
		beq	util_set_led_delay_exit ; it's 2
		mov.w   #LED_DELAY_INSTANT,r0	; Must be 3
util_set_led_delay_exit:
                mov.w   r0,@led_delay_time_value
                rts
;                		                
; ---------------------------------------------------------
;
;;       Set the LED delay, based on current_LED_speed.
;;       passed in r1l.
;
;util_set_led_delay:
;		and	#h'03,r1l		; make 0 to 3
;                cmp.b   #0,r1l
;                bne     util_set_led_delay_1
;                mov.w   #LED_DELAY_SLOW,r0
;                bra     util_set_led_delay_exit
;util_set_led_delay_1:
;                cmp.b   #1,r1l
;                bne     util_set_led_delay_2
;                mov.w   #LED_DELAY_MED,r0
;                bra     util_set_led_delay_exit
;util_set_led_delay_2:
;                cmp.b   #2,r1l
;                bne     util_set_led_delay_3
;                mov.w   #LED_DELAY_FAST,r0
;                bra     util_set_led_delay_exit
;util_set_led_delay_3:
;                cmp.b   #3,r1l
;                bne     util_set_led_delay_default
;                mov.w   #LED_DELAY_INSTANT,r0
;                bra     util_set_led_delay_exit
;util_set_led_delay_default:
;                mov.w   #LED_DELAY_INIT,r0
;                mov.b   #LED_speed_INIT,r1l
;util_set_led_delay_exit:
;                mov.w   r0,@led_delay_time_value
;                rts
; ---------------------------------------------------------

;       Called only from p_led_ring process
;       Not true

;       Convert doppler degrees to LED values.
;       Handles LED double step, if required.
;       Params  = r1h blink bit, if needed (h'80)
;               = r1l doppler degrees
util_set_dop_deg_to_led:			; Adj for zero at 
						; top of display
		mov.b	r1l,r1l			; test 4 zero
		beq	make_it_199
		dec	r1l
						; ok for all values
		bra	no_led_adj		; except 0
make_it_199:
		mov.b	#199,r1l

no_led_adj:
;       If the LEDs haven't changed, don't need to do anything

                mov.w   @led_target,r0
                cmp.w   r0,r1
                bne     util_set_dop_deg_do_work
                rts

util_set_dop_deg_do_work:
                push    r2
                push    r3
                mov.w   r1,r3                   ; Save dopper degrees


;       If the LED display time delay is set to 3 instantaneous
;       then don't do the single stepping calculations
;	If 3 then instantaneous		
;       If 4 or 5 or 6 then check Q.
;       If Q 1 or more then GOTO instantaneous util_set_dop_do_uncorrected_work
;	If Q = 0 then make LED Speed 0 or 1 or 2
;
		mov.b   @current_LED_speed,r0l
		cmp.b	#3,r0l
		beq     util_set_dop_do_uncorrected_work
		blo	LED_do_slow		
		mov.b	@doppler_qual_0T9,r2l
		mov.b	@current_Threshold,r2h	; Q threshold set 1 to 5 
		cmp.b	r2h,r2l
		bhs	util_set_dop_do_uncorrected_work
;
;	Led speed 4,5 or 6 and Q = 0
;
		add.b	#0-4,r1l		; same as -4
			
	
LED_do_slow:
;	Check timer 
		mov.w   @rt_msec_led_ring_process,r3
		bne	LED_time_not_up
;		mov.w	@led_delay_time_value,r3
;		mov.w   r3,@rt_msec_led_ring_process
		
;       Move one step toward the direction required.
;
                mov.b   #0,r1h			; r1 now word new location
                mov.w   @led_target,r2		; last target location
;
                mov.b   #0,r2h			; should be 0 already
                mov.w   #100,r3			; Error NO!

;       1/2 #of LEDs around circle

                jsr     util_calc_dir_vector	; r0h  CW = 0 | CCW = 1
                mov.w   @led_target,r2
                mov.b   #0,r2h
                mov.w   #1,r1
                cmp.b   #CW,r0h
                beq     util_set_dop_incr
util_set_dop_decr:
                sub.w   r1,r2
                bcc     util_set_dop_save_target
                mov.b   #199,r2l
;       Correct for undeflow
                bra     util_set_dop_save_target
util_set_dop_incr:
                add.w   r1,r2
                mov.w   #200,r1
                cmp.w   r1,r2
                blo     util_set_dop_save_target
;       Correct for overflow
                mov.b   #0,r2l

util_set_dop_save_target:
                mov.b   r2l,r1l

util_set_dop_do_uncorrected_work:
                mov.b   r3h,r1h
                mov.w   r1,@led_target
                mov.b   #LED_UNUSED_LOCATION,r0h
                mov.b   r1l,r0l
                shlr    r0l
                shlr    r0l
                bcc     util_set_dop_deg_secondary
                mov.b   r0l,r0h
                add.b   #1,r0h
                cmp.b   #50,r0h
                blo     util_set_dop_deg_secondary
                mov.b   #0,r0h
util_set_dop_deg_secondary:
                or      r3h,r0l
                or      r3h,r0h
                mov.b   r0l,@led_primary
                mov.b   r0h,@led_secondary
                mov.w	@led_delay_time_value,r3
		mov.w   r3,@rt_msec_led_ring_process
LED_time_not_up:
                pop     r3
                pop     r2
                rts
; ---------------------------------------------------------



; ---------------------------------------------------------

init_show_antenna_config:

                mov.b   @antenna_failure,r0l
                beq     init_show_antenna_ok

;       Display AE #
                mov.w   #led_7_marquee,r0
;       "A"
                mov.b   #SEG_PAT_A,r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       "E"
                mov.b   #SEG_PAT_E,r1l
                mov.b   r1l,@r0
                adds    #1,r0

;       Set the pattern for the number of elements
;       This reference only works because it was
;       just set in init_data

                mov.b   @antenna_failure,r1l

                mov.b   r1l,@r0

;       Start the display
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
                mov.b   #3,r0l
                mov.b   r0l,@led_7_marquee_length
                rts

;       Display AC # H/L

init_show_antenna_ok:
                mov.w   #led_7_marquee,r0
;       "A"
                mov.b   #SEG_PAT_A,r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       "C"
                mov.b   #SEG_PAT_C,r1l
                mov.b   r1l,@r0
                adds    #1,r0

;       Set the pattern for the number of elements
;       This reference only works because it was
;       just set in init_data

                mov.b   @antenna_configuration,r1l
                and     #h'f0,r1l
                shlr    r1l
                shlr    r1l
                shlr    r1l
                shlr    r1l
                mov.b   r1l,@r0
                adds    #1,r0

;       High/Low for switching
;       This reference only works because it was just
;       set in init_data

                mov.b   @antenna_configuration,r1l
                and     #h'0f,r1l
                beq     init_show_antenna_low
                mov.b   #SEG_PAT_H,r1l
                bra     init_show_done
init_show_antenna_low:
                mov.b   #SEG_PAT_L,r1l
init_show_done:
                mov.b   r1l,@r0
;       Start the display
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
                mov.b   #4,r0l
                mov.b   r0l,@led_7_marquee_length
                rts

; ---------------------------------------------------------

;       Play start up tone

init_tone:
                mov.b   @ctrl_byte_Start_tone,r1L
                beq     main_play_no_tone

                mov.w   #sound_queue,r1

                mov.b   @antenna_failure,r0l
                bne     main_play_not_so_good_tone

;       Play the "I am OK, you are OK message"

;       To make this work:

;       The low  byte = tone ff being the lowest
;       The high byte = time if below 128 then 256X mS
;                            if 128 or higher then 128 = 127 mS
;                            and it goes lower.  Good for click
;       Place the word in the "sound_queue"  Will hold 10

;       Then set "sound_length" to the number of tones played.
;       Then set "sound_position" to zreo

main_play_the_oh_so_good_tone:

                mov.w   #H'31a,r0       ; send a "G"
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #h'101,r0       ; 2
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #H'31a,r0       ; 3
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #h'101,r0       ; 4
                mov.w   r0,@r1

                adds    #2,r1
                mov.w   #H'11a,r0       ; 5
                mov.w   r0,@r1
                
                adds    #2,r1

                mov.w   #h'101,r0       ; 6
                mov.w   r0,@r1                

                mov.b   #6,r0l
                mov.b   r0l,@sound_length
                mov.b   #0,r0l
                mov.b   r0l,@sound_position
                mov.b   #PROCESS_RUN,r0l
                mov.b   r0l,@ps_sound_driver
main_play_no_tone:
                rts


main_play_not_so_good_tone:

                mov.w   #H'11b,r0       ; send an "F"
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #h'101,r0       ; 2
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #H'11b,r0       ; 3
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #h'101,r0       ; 4
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #H'31b,r0       ; 5
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #h'101,r0       ; 6
                mov.w   r0,@r1

                adds    #2,r1

                mov.w   #H'11b,r0       ; 7
                mov.w   r0,@r1
                
                adds    #2,r1
                
                mov.w   #h'101,r0       ; 8 
                mov.w   r0,@r1                



;       Initiate the start tone

                mov.b   #8,r0l
                mov.b   r0l,@sound_length
                mov.b   #0,r0l
                mov.b   r0l,@sound_position
                mov.b   #PROCESS_RUN,r0l
                mov.b   r0l,@ps_sound_driver
                rts

; ---------------------------------------------------------

;       Stepper maintenence

; Find the zero point of the stepper

;       This routine first checks to see if the pointer is
;       already at zero. If it is, step a few steps, to get away
;       from zero, then do a normal step loop. Otherwise
;       we will not know where zero really is.

;       WARNING: This routine will not preserve
;       any registers except for r5 and up.

zero_stepper:

;       Pre step the pointer to synch up the motor, and
;       make sure the sensor is not over the radiator.
;       If the motor is not synchronized with the processor,
;       the motor might actually step backwards, setting
;       the over the radiator flag, giving bad pointer
;       calibration.

zero_do_full_loop:

;       If we step more than 500 times, it will never work,
;       so skip the stepper motor.

                mov.w   #500,r3

;       500 Steps and we will bail out.

zero_do_step:

;       NOTE: Do not try to optimize this loop by taking out the
;             cmp.w statement. "subs" sets no condition flags.
;	NOTE: if testing for zero mov.w r2,r2 will set flags

                mov.w   @pointer_delay,r2

zero_wait_step:
                subs    #1,r2
                mov.w   r2,r2
                bne     zero_wait_step

                mov.b   #1,r1h          ; Turn lamps off
                mov.b   #CCW,r1l
                jsr     stepper_single_step

;       Check to see if we went too far

                subs    #1,r3
                mov.w   r3,r3
                beq     zero_abort

;       Check for over the radiator
                mov.b   @h'ffc1,r1l
                btst    #2,r1l          ; radiator_bit
                beq     zero_do_step
; Ok we got zero bit change
                

;       Step more the CCW direction,

                mov.b   #10,r4l		; about right until ccw cal

zero_width_do_step:
                mov.w   @pointer_delay,r2
zero_width_wait_step:
                subs    #1,r2
                mov.w	r2,r2
                bne     zero_width_wait_step
;
                mov.b   #1,r1h          ; Turn lamps off
                mov.b   #CCW,r1l
                jsr     stepper_single_step

;       Make sure the stepper is not stuck.

                dec	r4l
                beq     zero_width_exit

                bra     zero_width_wait_step

zero_width_exit:
                rts

zero_abort:
                mov.w   #str_point_no_zero,r1
                jsr     @@writeln_buffered_str
                mov.b   #0,r0l
                mov.b   r0l,@h'ffc1
                rts


; ---------------------------------------------------------

;       r1l contains the character value of the 7 segment
;       display character.
;       The value is used as an index into the pattern
;       table and the address is placed into the
;       active pattern address.

;       This routine is called only from p_led_driver

set_7seg_pattern:

                mov.b   #0,r1h
                shll    r1l
                mov.w   #led_7seg_patterns,r0
                add.w   r0,r1                   ; Pattern[idx]
                mov.w   @r1,r0                  ; Get address of new pattern

;       Before stuffing, see what pattern is already there.
;       If it is the same, don't bother reseting.
;       If the new pattern is stuffed in, and
;       the segment index is reset,the LED multiplexor
;       won't cycle correctly.

;       When this happens, only one 7 segment turns on,
;       and the primary doesn't show.

;       This demonstrated when "force_7seg" is called
;       continously, such as for the "hold" operation.
;       So... check to see if it is the same.

;       If so, exit the routine

                mov.w   @led_7seg_pattern,r1
                cmp.w   r1,r0
                beq     set_7seg_pattern_exit

                mov.w   r0,@led_7seg_pattern
                mov.b   #0,r0l

;       Start the character display @ begining

                mov.b   r0l,@led_7_seg_idx
set_7seg_pattern_exit:
                rts

;
; ---------------------------------------------------------

oc1b_srvc:                                                                      ; ISR
                                                                                ; ISR
;       Interrupt Routine                                                       ; ISR
                                                                                ; ISR
;       THIS IS IT THE REAL ISR                                                 ; ISR
                                                                                ; ISR
;       Reset to allow  next int                                                ; ISR
                                                                                ; ISR
                bclr    #timer_16b_ocfb,@timer_16b_csr                          ; ISR
                                                                                ; ISR
;       This interrupt routine gets the next antenna state                      ; ISR
;       information from the antenna state table                                ; ISR
;       (@r5) and works with it.                                                ; ISR
                                                                                ; ISR
;       The antenna table looks like:                                           ; ISR
;               word( antenna_pattern, highbyte=switch high, lobyte=switch lo ) ; ISR
;               byte( antenna number) byte( next switch time )                  ; ISR
;               word( next_state )                                              ; ISR
                                                                                ; ISR
                push    r0                                                      ; ISR
                push    r1                                                      ; ISR
                push    r2                                                      ; ISR
                                                                                ; ISR
;----------------------------------------------------------                     ; ISR
;	timing_test                                                             ; ISR
;                mov.w   #h'7ff7,r1      ; By rjh turns on extra pin            ; ISR
                                        ; on the Hitachi board                  ; ISR
;                bset    #6, @r1         ; the time the led is on               ; ISR
                                        ; is the time spent in the isr          ; ISR
                                                                                ; ISR
;       Used to find out how much time is used in the int                       ; ISR
                                                                                ; ISR
;----------------------------------------------------------                     ; ISR
                                                                                ; ISR
;       Set the pattern for antenna switches.                                   ; ISR
;       The plan here is to do a "make before break".                           ; ISR
;       What this means is, set the next antenna before                         ; ISR
;       turning off the previous antenna.                                       ; ISR
;       This has better detection characteristics                               ; ISR
;       in the radio discriminator.                                             ; ISR
                                                                                ; ISR
;       To do this, pick up the old output value,                               ; ISR
;       and combine it with the next value.                                     ; ISR
;       Then set the final value.                                               ; ISR
                                                                                ; ISR
;               Previous value  = r1h                                           ; ISR
;               Next value      = r0                                            ; ISR
;                                                                               ; ISR
;       Then combine old and new                                                ; ISR
;       Combined value = r1h                                                    ; ISR
;                                                                               ; ISR
;       Then set new value only                                                 ; ISR
;       New value = r1l                                                         ; ISR
;                                                                               ; ISR
                mov.w   @r5+,r0 ; Switch pattern                                ; ISR
                mov.w   @r5,r1  ; State number / time-out time                  ; ISR
                                                                                ; ISR
;        if( hold_mode )                                                        ; ISR
;               flush_queue                                                     ; ISR
;        else                                                                   ; ISR
;        {                                                                      ; ISR
;               if( antenna_state == 1 )                                        ; ISR
;                       call queue                                              ; ISR
;               set_new_antenna_state & pattern                                 ; ISR
;        }                                                                      ; ISR
;                                                                               ; ISR
;        If the hold button is in effect, do not rotate the anntennas.          ; ISR
;        This will prevent the omnipresent "doppler whine" when the             ; ISR
;        user transmits using another transmitter located nearby.               ; ISR
                                                                                ; ISR
                mov.b   @ctrl_byte_hold,r2L                                     ; ISR
                bne     isr_set_timer                                           ; ISR
                mov.b   @ctrl_byte_PTT,r2L                                      ; ISR
                bne     isr_set_timer                                           ; ISR
                                                                                ; ISR
;       If hold do not rotate antennas                                          ; ISR
                                                                                ; ISR
;       Only queue the signal once per rotation.                                ; ISR
                                                                                ; ISR
isr_check_ant_1:
		mov.b	@tenna_port,r2l						; ISR
										; ISR
		and	#h'0f,r2l                                               ; ISR
		cmp.b	#h'0e,r2l		; is it active low ant1?        ; ISR
		beq	ant1_active                                             ; ISR
		cmp.b	#1,r2l			; is it active high ant1?       ; ISR
		beq	ant1_active                                             ; ISR
		mov.b	@ant_one_flag,r2l                                       ; ISR
		beq     isr_not_antenna_one                                     ; ISR
check_end_pulse:                                                                ; ISR
		mov.b	@tenna_port,r2l						; ISR
		and	#h'0f,r2l                                               ; ISR
		cmp.b	#h'0d,r2l		; is low over ant1?             ; ISR
		beq	ant1_over						; ISR
		cmp.b	#2,r2l			; is high over ant1?            ; ISR
		bne     isr_not_antenna_one                                     ; ISR
ant1_over:                                                                      ; ISR
		mov.b	#2,r2l                                                  ; ISR
		mov.b	r2l,@ant_one_flag	; flag as over                  ; ISR
		bra	isr_not_antenna_one                                     ; ISR
ant1_active:                                                                    ; ISR
		mov.b	#1,r2l                                                  ; ISR
		mov.b	r2l,@ant_one_flag	; flag as active                ; ISR
;		bra	isr_not_antenna_one                                     ; ISR
                                                                                ; ISR
isr_not_antenna_one:                                                            ; ISR
                mov.b   @tenna_port,r1h                                         ; ISR
                mov.b   @antenna_configuration,r1l                              ; ISR
                and     #h'0f,r1l                                               ; ISR
                beq     isr_combine_switch_low                                  ; ISR
;                                                                               ; ISR
isr_combine_switch_high:                                                        ; ISR
                or      r0h,r1h                                                 ; ISR
                mov.b   r1h,@tenna_port                                         ; ISR
                mov.b   r0h,r1l                                                 ; ISR
                bra     isr_clear_combined_value                                ; ISR
;                                                                               ; ISR
isr_combine_switch_low:                                                         ; ISR
                and     r0l,r1h                                                 ; ISR
                mov.b   r1h,@tenna_port                                         ; ISR
                mov.b   r0l,r1l				; 2			; ISR
                bra     isr_clear_combined_value	; 4			; ISR
                                                                                ; ISR
;       At this point, the combine value has been in                            ; ISR
;       the output register for "mov.b" + "bra" cycles.                         ; ISR
;       Is this enough, or do we need to put some                               ; ISR
;       "no op" instructions in here?                                           ; ISR
                                                                                ; ISR
;       6 to 8 microSeconds. Perhaps? WHAT!					; ISR
;	Try 1uS                                                                 ; ISR
;       This is not a good way to do overlap                                    ; ISR
;       User has no controll of overlap time!                                   ; ISR
;	Overlap controll not needed						; ISR
;	Tested from 2.5 uS to about 15 uS with no change			; ISR
                                                                                ; ISR
isr_clear_combined_value:							; ISR
;		mov.b	@overlap_time,r0h		; 6			; ISR
;		beq	overlap_off			; 4			; ISR
;overlap_loop:									; ISR
;		dec	r0h				; 2			; ISR
;		bne	overlap_loop			; 4			; ISR
										; ISR
overlap_off:									; ISR
                mov.b   r1l,@tenna_port			; 4			; ISR
;							; 2 uS if overlap = 0	; ISR
;							; + overlap_time X .3	; ISR
;  3 = 2.9 uS   6 = 3.8 uS   A = 5.0 uS   D = 5.9 uS  10 = 6.8 uS		; ISR
; 14 = 8.0 us  17 = 8.9 uS  1A = 9.8 us  1E = 11 uS				; IRS
                                                                                ; ISR
isr_set_timer:                                                                  ; ISR
;       Set the timer time-out                                                  ; ISR
                                                                                ; ISR
                mov.w   @r5+,r0                                                 ; ISR
                mov.b   #0,r0h                                                  ; ISR
                                                                                ; ISR
;       Get rid of start of table flag.                                         ; ISR
                                                                                ; ISR
;       Place next count (int value) in output compare reg                      ; ISR
                                                                                ; ISR
                mov.w   r0,@timer_16b_ocr_AB                                    ; ISR
                                                                                ; ISR
;       Point to the next state                                                 ; ISR
                                                                                ; ISR
                mov.w   @r5,r0                                                  ; ISR
                mov.w   r0,r5                                                   ; ISR
                                                                                ; ISR
outnoint:                                                                       ; ISR
;        mov.w   #h'7ff7,r1                                                     ; ISR
;        bclr    #6,@r1  ; led off  timing_test                                 ; ISR
                                                                                ; ISR
                pop     r2                                                      ; ISR
                pop     r1                                                      ; ISR
                pop     r0                                                      ; ISR
                rte                                                             ; ISR
;
;----------------------------------------------------------
;
;	Uses PWM timer for real time clock
;	test for 2 mS count
;	Uses
;		r0
;		r1
;		r2
;
;----------------------------------------------------------

rt_clock_update:

                mov.b   @PWM1_tcnt,r1l
                cmp.b   #159,r1l		; 2mS? 156 for 20.0000 MHz 1.99992 mS
                				;      159 for 19.6608 MHz 2.0034 mS
                bcc     rt_clock_update_now

                rts
                
rt_clock_update_now:
           
                mov.b   #PWM1_reset,r1l
                mov.b   r1l,@PWM1_tcr
                mov.b   #PWM1_start,r1l
                mov.b   r1l,@PWM1_tcr
                jsr     rt_os_timers
                mov.w   @rt_clock_msec,r0
                adds    #2,r0
                mov.w   r0,@rt_clock_msec
                mov.w   #1000,R1                ; one sec?
                sub.w   R1,R0
                bmi     rtc_no_more_inc
                mov.w   r0,@rt_clock_msec

;       Incr Sec

                mov.b   @rt_clock_sec,r0l
                inc     r0l
                mov.b   r0l,@rt_clock_sec
                mov.b   #0,R0h
                mov.w   R0,@rt_clock_sec_change_flag
                mov.b   #60,R0h
                sub.b   R0h,R0L                 ; one min?
                bne     rtc_no_more_inc
                mov.b   R0L,@rt_clock_sec

;       Incr Min

                mov.b   @rt_clock_min,R0L
                inc     r0l
                mov.b   r0l,@rt_clock_min
                mov.b   #60,R0h
                sub.b   R0h,R0L                 ; one hr?
                bne     rtc_no_more_inc
                mov.b   R0L,@rt_clock_min

;       Incr hours (do not care about carry condition here)

                mov.w   @rt_clock_hour,R0
                adds    #1,R0
                mov.w   R0,@rt_clock_hour

rtc_no_more_inc:
rt_os_timers:
;        Decrement real time process timers here
;        If and when the timers read zero, leave them at zero

;       Blank for adding timer

;               mov.w   @,r2
;               beq     ck_rt_msec_
;               sub.w   R0,R2
;               mov.w   R2,@rt_msec_
;               bne     ck_rt_msec_sounder
;       Timer exicute code  *******************
;
                mov.w   #1,R0                   ; use to dec timers

;       Add new timer here connect to next timer

                mov.w   @rt_msec_but_2nd,r2
                beq     ck_rt_msec_sounder
                sub.w   R0,R2
                mov.w   R2,@rt_msec_but_2nd
                bne     ck_rt_msec_sounder

;       Timer exicute code
                    mov.b       @but_number_stor,r2L
                    beq ck_rt_msec_sounder      ; no button value
                    mov.b       #8,r2h          ; add 8 to button
                    add.b       r2h,r2L
                    mov.b       r2L,@but_number_stor

ck_rt_msec_sounder:
                mov.w   @rt_msec_sounder,r2
                beq     ck_rt_msec_marquee
                sub.w   R0,R2
                mov.w   R2,@rt_msec_sounder

ck_rt_msec_marquee:
                mov.w   @rt_msec_marquee,r2
                beq     ck_rt_msec_attractor
                sub.w   R0,R2
                mov.w   R2,@rt_msec_marquee

ck_rt_msec_attractor:
                mov.w   @rt_msec_attractor,r2
                beq     ck_rt_msec_lcd
                sub.w   R0,R2
                mov.w   R2,@rt_msec_attractor
ck_rt_msec_lcd: 

                mov.w   @rt_msec_lcd,r2
                beq     ck_rt_msec_stepper
                sub.w   R0,R2
                mov.w   R2,@rt_msec_lcd

ck_rt_msec_stepper:
                mov.w   @rt_msec_stepper,r2
                beq     ck_rt_msec_alarm_process
                sub.w   R0,R2
                mov.w   R2,@rt_msec_stepper

ck_rt_msec_alarm_process:
                mov.w   @rt_msec_alarm_process,r2
                beq     ck_rt_msec_led_ring_process
                sub.w   R0,R2
                mov.w   R2,@rt_msec_alarm_process

ck_rt_msec_led_ring_process:
                mov.w   @rt_msec_led_ring_process,r2
                beq     ck_rt_msec_antenna_check	; it's at Zero do nothing
                sub.w   R0,R2				; dec
                mov.w   R2,@rt_msec_led_ring_process	; put it back

ck_rt_msec_antenna_check:
                mov.w   @rt_msec_ant_chk,r2
                beq     no_more_msec_checks
                sub.w   R0,R2
                mov.w   R2,@rt_msec_ant_chk
                bne     no_more_msec_checks

;       Timer exicute code

                jsr     ant_chk_adc_read

no_more_msec_checks:
                mov.w   #1,R0
		
                rts


rt_clock_change_sec:
                mov.w   #0,R0
                mov.w   R0,@rt_clock_sec_change_flag

;       clear change flag
;       use to dec timers

                mov.w   #1,R0
                mov.w   @rt_sec_alarm,r1
                beq     ck_rt_sec_snooper
                sub.w   R0,R1
                mov.w   R1,@rt_sec_alarm

ck_rt_sec_snooper:
                mov.w   @rt_sec_snooper,r1
                beq     ck_rt_sec_init
                sub.w   R0,R1
                mov.w   R1,@rt_sec_snooper

ck_rt_sec_init:
                mov.w   @rt_sec_init,r1
                beq     ck_rt_sec_gps
                sub.w   R0,R1
                mov.w   R1,@rt_sec_init                

ck_rt_sec_gps:
                mov.w   @rt_sec_gps,r1
                beq     ck_rt_turn_on_uart_rx
                sub.w   R0,R1
                mov.w   R1,@rt_sec_gps
ck_rt_turn_on_uart_rx:
		mov.w   @rt_sec_uart_turn_on,r1
                beq     no_more_ck_rt_sec
                sub.w   R0,R1
                mov.w   r1,@rt_sec_uart_turn_on
                bne	no_more_ck_rt_sec
						; serial_status_val
		mov.b   #h'30,r0l		; start rx uart0
                mov.b   r0l,@s0_serial_cntrl
;                mov.b	@s0_serial_status_reg,r0l
;                mov.b	#0,r0l
;                mov.b	r0l,@s0_serial_status_reg

no_more_ck_rt_sec:
                rts

process_filters:

filt_0:


;----------------------------------------------------------

;       No filtering going on just take the data and display it.

;----------------------------------------------------------

                mov.b   @qsync_bearing,r1L
                mov.b   #0,r1h
                mov.w   r1,@filt_0_output

                mov.b   @gps_heading_dd,r0L
                mov.b   #0,r0H
                add.w   r0,r1
                mov.w   #200,r0
                cmp.w   r0,r1
                bcs     filt_0_done
                sub.w   r0,r1

filt_0_done:
		mov.b	@gps_speed_flag,r0l
		beq	filt_1			; do not update if slow
                mov.w   r1,@filt_0_A_output
;
;**********************************************************
;
filt_1:
;
;----------------------------------------------------------
;
;       Very simple filter 
;	Do not display Q = zero
;	Use Q threshold
;
;----------------------------------------------------------
;
		mov.b   @doppler_qual_0T9,r0l
		mov.b	@current_Threshold,r0h	; Q threshold set 1 to 5 
		cmp.b	r0h,r0l
		blo	filt_1_exit		; Q too low
                mov.b   @qsync_bearing,r1L
                mov.b   #0,r1h
                mov.w   r1,@filt_1_output

                mov.b   @gps_heading_dd,r0L
                mov.b   #0,r0H
                add.w   r0,r1
                mov.w   #200,r0
                cmp.w   r0,r1
                bcs     filt_1_done
                sub.w   r0,r1

filt_1_done:
		mov.b	@gps_speed_flag,r0l
		beq	filt_2			; do not update if slow
                mov.w   r1,@filt_1_A_output
filt_1_exit:
;                
;**********************************************************
;
filt_2:
;	Use threshold and sample size
;	Sample size is the number of doppler points
;	that are the same.
;	Q threshold, Q has to be GT or = to count
;
;
		mov.b   @doppler_qual_0T9,r0l
		mov.b	@current_Threshold,r0h	; Q threshold set 1 to 5 
		cmp.b	r0h,r0l
		bhs	filt_2_Q_ok		; Q too low
		mov.b	#0,r0l
		mov.b	r0l,@good_Q_count	; reset good count
		bra	filt_2_exit		; Q too low
filt_2_Q_ok		
		mov.b	@good_Q_count,r0l
		inc	r0l
		mov.b	@current_sample_number,r0h
		add.b	r0h,r0h			; count 2,4,6,8,10
		cmp.b	r0h,r0l			; do we have enough?
		bhs	filt_2_S_ok
		mov.b	r0l,@good_Q_count
		bra	filt_2_exit
filt_2_S_ok:		
                mov.b   @qsync_bearing,r1L
                mov.b   #0,r1h
                mov.w   r1,@filt_2_output

                mov.b   @gps_heading_dd,r0L
                mov.b   #0,r0H
                add.w   r0,r1
                mov.w   #200,r0
                cmp.w   r0,r1
                bcs     filt_2_done
                sub.w   r0,r1

filt_2_done:
		mov.b	@gps_speed_flag,r0l
		beq	filt_2_exit		; do not update if slow
                mov.w   r1,@filt_2_A_output
filt_2_exit:
;
;**********************************************************
;
;	If differance of average to new bearing is GT 100
;	Inc bad count and exit
;	If bad count too big reset average to zero and start over
;	If a good bearing then add to average and zero bad count
;	Use Q weighted averge
;	Keep average in +100 form and correct the output
;	Use sample size to dynamicly control sample size
;	Use Q level 
;
;			Add 100
;       		  100
;			 ______  
;	                /      \ 
; 	               / Front  \
;                   50 |________| 150
;                      |        |
;                      \        /
;	                \______/ 
;			   |
;			 0 - 199
;
filt_3:
		mov.b   @doppler_qual_0T9,r0l
		mov.b	@current_Threshold,r0h	; Q threshold set 1 to 5 
		cmp.b	r0h,r0l
		blo	filt_3_exit2		; Q too low
                mov.b   @qsync_bearing,r1L
                cmp.b	#100,r1l		; add or sub 100
                beq	filt_3_DD100_exit
                blo	filt_3_plus_100
                add.b	#256 - 100,r1l		; sub #100
                bra	filt_3_add_done
filt_3_plus_100:
		add.b	#100,r1l
filt_3_add_done:				; bearing now 0 rear
		mov.b	r1l,@filt_3_new_b	; save new b +100
;		
		mov.b	@filt_3_sample_cnt,r0h
		beq	filt_3_hi_ok		; filter empty or start over
		mov.b	@filt_3_average_b,r1h	; find range of allowed new bearing
		cmp.b	#100,r1h		; if above 99 then pos lim = 199
		bhs	filt_3_199
		add.b	#100,r1h
		cmp.b	#200,r1h
		blo	filt_3_p_lim_set
filt_3_199:		
		mov.b	#199,r1h
filt_3_p_lim_set:
		mov.b	@filt_3_average_b,r1l		
		add.b	#256 - 100,r1l		; sub #100
		bhi	filt_3_n_lim_set
		mov.b	#0,r1l
filt_3_n_lim_set:
						; r1l = min value bearing
						; r1h = max value bearing
		mov.b	@filt_3_new_b,r0l
		cmp.b	r1l,r0l
		blo	filt_3_bad
filt_3_low_ok:
		cmp.b	r1h,r0l
		bls	filt_3_hi_ok
filt_3_bad:		
		mov.b	@filt_3_bad_cnt,r1l
		inc	r1l
		mov.b	r1l,@filt_3_bad_cnt
		cmp.b	#FILT_3_BAD_MAX,r1l
		blo	filt_3_hi_ok
filt_3_DD100_exit:		
		mov.b	#0,r1l
		mov.b	r1l,@filt_3_bad_cnt
		mov.b	r1l,@filt_3_sample_cnt
		mov.b	#0,r1h
		mov.w	r1,@filt_3_ave_total
filt_3_exit2:		
		jmp	filt_3_exit
filt_3_hi_ok:
		mov.b	@filt_3_new_b,r1l
		mov.b   @doppler_qual_0T9,r0l	
		mulxu	r0l,r1
		mov.w	@filt_3_ave_total,r0
		add.w	r1,r0
		mov.w	r0,@filt_3_ave_total
		mov.b   @doppler_qual_0T9,r0l
		mov.b	@filt_3_sample_cnt,r1l
		add.b	r0l,r1l
		mov.b	r1l,@filt_3_sample_cnt
		mov.b	@current_sample_size,r1h
		cmp.b	r1h,r1l
		bls	filt_3_no_del
		mov.w	@filt_3_ave_total,r0
		mov.b	@filt_3_average_b,r1l
		mov.b	#0,r1h
		add.w	r1,r1
		add.w	r1,r1
		add.w	r1,r1
		add.w	r1,r1
		sub.w	r1,r0
		mov.w	r0,@filt_3_ave_total
		mov.b	@filt_3_sample_cnt,r1l
		add.b	#256 - 16,r1l
		mov.b	r1l,@filt_3_sample_cnt
filt_3_no_del:
		mov.w	@filt_3_ave_total,r1
		mov.b	@filt_3_sample_cnt,r0l
		divxu	r0l,r1
		mov.b	r1l,@filt_3_average_b
						; convert back to 0 front
                cmp.b	#100,r1l		; add or sub 100
                blo	filt_3A_plus_100
                add.b	#256 - 100,r1l		; sub #100
                bra	filt_3A_add_done
filt_3A_plus_100:
		add.b	#100,r1l
filt_3A_add_done:
                mov.b   #0,r1h
                mov.w   r1,@filt_3_output

                mov.b   @gps_heading_dd,r0L
                mov.b   #0,r0H
                add.w   r0,r1
                mov.w   #200,r0
                cmp.w   r0,r1
                bcs     filt_3_done
                sub.w   r0,r1

filt_3_done:
		mov.b	@gps_speed_flag,r0l
		beq	filt_3_exit		; do not update if slow
                mov.w   r1,@filt_3_A_output
filt_3_exit:                
                
;**********************************************************
;
filt_4:
;	Front only +or- 90 degrees (150-0-50) add 50 to
;	dd if 0 to 49 subtract 100 from bearings 150 or more 
;	and do a standard average of 0 to 99
;	use quality by mult the bearing
;	keep track of quality total to get average
;	subtract 50 from average
;	do a running average. Keep running total when the
;	Use 16 samples keep Q Bearing as a sample.
;	fifo the buffer and remove the output from the average
;	and add the new sample.
;	If bearing is to the rear just pass it thru.
;
		mov.b   @doppler_qual_0T9,r0l
		mov.b	@current_Threshold,r0h	; Q threshold set 1 to 5 
		cmp.b	r0h,r0l
		bhs	filt_4_Q_ok
		jmp	filt_4_exit
filt_4_Q_ok:
		mov.b   @qsync_bearing,r1L	; get bearing
		cmp.b	#50,r1l
		blo	in_front
		cmp.b	#150,r1l
		bhs	in_front
		mov.w	#0,r0
		mov.w	r0,@Bearing_sum		; if to rear start over
		mov.b	r0l,@q_sum
		bra	output_bearing
in_front:
		mov.b   @doppler_qual_0T9,r0l
		bne	add_50
		jmp	filt_4_exit		; quality zero 
add_50:						; don't do anything
		add.b	#50,r1l			; right quad ok
						; 50-99
		cmp.b	#100,r1l		; is it below 100?
		blo	bear_ok
						; 150 -199
		add.b	#56,r1l			; left quad
						; now bearing should
						; be 0 to 99
bear_ok:
	; Now have bearing 0-99 (front) in r1l and Q in r0l
	; Do an average of front bearings.
	;
		mulxu	r0l,r1			; Q times Bearing
		mov.w	@Bearing_sum,r0
		add.w	r0,r1
		mov.w	r1,@Bearing_sum		; Bearing total
		mov.b   @doppler_qual_0T9,r0l		
		mov.b	@q_sum,r0h
		add.b	r0l,r0h			; sum Q
		mov.b	r0h,@q_sum
		mov.b	r0h,r0l
		divxu	r0l,r1			; make average r1l
		mov.b	@current_sample_size,r0h
		cmp.b	r0h,r0l			; too many samples?
		blo	sample_num_ok
;		
	; Ok we have to remove some samples
	; take the average and mult it by 16 and remove 16 samples from
	; q_sum and the product from Bearing_sum
;
		push	r1
		mov.b	#0,r1h
		add.w	r1,r1
		add.w	r1,r1
		add.w	r1,r1
		add.w	r1,r1			; Times 16
		mov.w	@Bearing_sum,r0
		sub.w	r1,r0			; remove 16 times average
		mov.w	r0,@Bearing_sum		; from the total
		mov.b	#16,r0l
		mov.b	@q_sum,r0h
		sub.b	r0l,r0h			; remove 16 samples
		mov.b	r0h,@q_sum
		pop	r1			; new bearing is back
sample_num_ok:
	; average now 0 to 99 but should be 150 - 0 - 49
		mov.b	#150,r1h
		add.b	r1h,r1l
		cmp.b	#200,r1l
		blo	output_bearing		; 150 to 199
		add.b	#56,r1l
output_bearing:
						; bearing in r1l
                mov.b   #0,r1h
                mov.w   r1,@filt_4_output

                mov.b   @gps_heading_dd,r0L
                mov.b   #0,r0H
                add.w   r0,r1
                mov.w   #200,r0
                cmp.w   r0,r1
                bcs     filt_4_done
                sub.w   r0,r1

filt_4_done:
		mov.b	@gps_speed_flag,r0l
		beq	filt_4_exit		; do not update if slow
                mov.w   r1,@filt_4_A_output
;
filt_4_exit:
;
filt_5:
;	bset	#1,@port_8
		mov.b	@filter_rot,r1l
		inc	r1l
		inc	r1l
		cmp	#max_filter - 2,r1l
		bls	filt_5_in_range
		mov.b	#0,r1l
		
filt_5_in_range:
		mov.b	r1l,@filter_rot
		mov.b	#0,r1h
		mov.w	#filt_0_output,r0
		add.w	r0,r1			; r1 now points to
						; filt_0 thru filt_last-1
						; depending on filter_rot
		mov.w	@r0,r1			; now have bearing from a filter
		mov.w	r1,@filt_5_output
filt_5_A:
		mov.b	@filter_rot,r1l				
		mov.b	#0,r1h
		mov.w	#filt_0_A_output,r0
		add.w	r0,r1			; r1 now points to
						; filt_0 thru filt_last-1
						; depending on filter_rot
		mov.w	@r0,r1			; now have bearing from a filter
		mov.w	r1,@filt_5_A_output
;	bclr	#1,@port_8		
				
;		rts
;
; ---------------------------------------------------------
;
Display_8LED:
;
;	Now that we have all filters data renewed
;	lets put it out to the LED8 display
;	There are 4 displays outer RED, outer GREEN, iner RED, and iner GREEN
;	RED uper nibble, GREEN lower nibble
;	Requires Odd and Even bytes for the outer and iner port 3
;	Positive transition clock on P81 for outer
;	Negitive transition clock on P81 for iner    
;
;	LED8_out_odd:		.res.b	1
;	LED8_out_even:		.res.b	1
;	LED8_iner_odd:		.res.b	1
;	LED8_iner_even:		.res.b	1
;
; 	LED8_out_RED:		.data.b  1	  
;	LED8_out_GREEN:		.data.b  2
;	LED8_iner_RED:		.data.b  3
;	LED8_iner_GREEN:	.data.b  4
;
;DD_to_LED
;	Convert DD to LED8
;	Input R0l filter number
;	output	r01 and r0h from table or 07
;
; ---------------------------------------------------------
;	
;	; Example
;			output 07 for RED outer - high nibble Flip-flop = 0
;		for even
;			required result 0000 ----
;		for odd
;			required result 0111 ----
;
;			output 12 for GREEN outer low  nibble Flip-flop = 0
;		for even
;			required result ---- 0001
;		for odd
;			required result ---- 0010
;
;			output 34 for RED iner - high nibble Flip-flop = 1
;		for even
;			required result  0011 ----
;		for odd
;			required result  0100 ----
;
;			output 56 for GREEN iner low  nibble Flip-flop = 1
;		for even
;			required result ---- 0101
;		for odd
;			required result ---- 0110
;	outer latch
;		for even		RED  GREEN
;			required result 0000 0001	Flip-flop = 0
;		for odd
;			required result 0111 0010	Flip-flop = 1
;	iner latch
;		for even
;			required result 0011 0101	Flip-flop = 0
;		for odd
;			required result 0100 0110	Flip-flop = 1
;
;	Flip_flop = 0    RED GREEN     RED  GREEN
;	   even positive clock	      |--------------------- Display 1 (07)
;			0000 0001     --0      1 outer
;	   even negitive clock        |             |
;			0011 0101     | 3    --5    |------- Display 2 (12)
;	Flip_flop = 1		      |  \   |      |
;	   odd  positive clock	      |   \  |      |
;			0111 0010     --7 /  | 2 outer
;	   odd  negitive clock		 /   |
;			0400 0110	4     --6 iner------ Display 4 (56
;					|------------------- Display 3 (34)
;
;	Data from display 1 goes in LED8_out_even  HN & LED8_out_odd HN
;	Data from display 2 goes in LED8_out_even  LN & LED8_out_odd LN
;	Data from display 3 goes in LED8_even_even HN & LED8_iner_odd HN
;	Data from display 4 goes in LED8_enen_even LN & LED8_iner_odd LN
;
;		LED8_out_odd	= 72
;		LED8_out_even	= 01
;		LED8_iner_odd	= 46
;		LED8_iner_even  = 35	
;
		mov.b	@LED8_out_RED,r0l	; Display 1
		jsr	DD_to_LED
						; if 07
						; r0l = 07
						; r0h = 70
						; need to place
						; r0l in LED8_out_even HN 
						; r0h in LED8_out_odd  HN
		and.b	#h'0f0,r0h
		and.b	#h'0f0,r0l
		mov.b	@LED8_out_even,r1l
		and.b	#h'0f,r1l
		mov.b	@LED8_out_odd,r1h
		and.b	#h'0f,r1h
		or	r0l,r1l
		or	r0h,r1h
		mov.b	r1l,@LED8_out_even
		mov.b	r1h,@LED8_out_odd


;
		mov.b	@LED8_out_GREEN,r0l	; Display 2
		jsr	DD_to_LED
						; need to place
						; LN in LED8_out_even LN 
						; HN in LED8_out_odd  LN
		and.b	#h'0f,r0h
		and.b	#h'0f,r0l
		mov.b	@LED8_out_even,r1l
		and.b	#h'0f0,r1l
		mov.b	@LED8_out_odd,r1h
		and.b	#h'0f0,r1h
		or	r0l,r1l
		or	r0h,r1h
		mov.b	r1l,@LED8_out_even
		mov.b	r1h,@LED8_out_odd

; Now do iner display
		mov.b	@LED8_iner_RED,r0l	; Display 3
		jsr	DD_to_LED
						; need to place
						; LN in LED8_out_even HN 
						; HN in LED8_out_odd  HN
		and.b	#h'0f0,r0h
		and.b	#h'0f0,r0l
		mov.b	@LED8_iner_even,r1l
		and.b	#h'0f,r1l
		mov.b	@LED8_iner_odd,r1h
		and.b	#h'0f,r1h
		or	r0l,r1l
		or	r0h,r1h
		mov.b	r1l,@LED8_iner_even
		mov.b	r1h,@LED8_iner_odd
;
		mov.b	@LED8_iner_GREEN,r0l
		jsr	DD_to_LED
						; need to place
						; LN in LED8_out_even LN 
						; HN in LED8_out_odd  LN
		and.b	#h'0f,r0h
		and.b	#h'0f,r0l
		mov.b	@LED8_iner_even,r1l
		and.b	#h'0f0,r1l
		mov.b	@LED8_iner_odd,r1h
		and.b	#h'0f0,r1h
		or	r0l,r1l
		or	r0h,r1h
		mov.b	r1l,@LED8_iner_even
		mov.b	r1h,@LED8_iner_odd
;
; ---------------------------------------------------------
;
;FlipFlop:
	mov.b	@FlipFlop,r1h
	beq	FlipFlop_was_0
					; must have been non zero
	mov.b	#0,r1h
	mov.b	r1h,@FlipFlop
					; do odd
	mov.b	@LED8_out_odd,r0l
	mov.b	r0l,@port3_dr
	bset	#1,@port_8		; Pos clock outer
	mov.b	@LED8_iner_odd,r0l
	mov.b	r0l,@port3_dr
	bclr	#1,@port_8
		rts
flipFlop_was_0:
	inc	r1h
	mov.b	r1h,@FlipFlop
					; do even
	mov.b	@LED8_out_even,r0l
	mov.b	r0l,@port3_dr
	bset	#1,@port_8		; pos clock iner
	mov.b	@LED8_iner_even,r0l
	mov.b	r0l,@port3_dr
	bclr	#1,@port_8
	rts
;		
; ---------------------------------------------------------
;
;       Given a rotation rate 0-9, set the time base value
;       Time base from 8 bit timer #1
;       Rate is 0-9 in r1l
;
;                             Entry with r1l new rot rate
set_rotation_rate:

                mov.b   r1l,@current_rotation_rate
                mov.b   #0,r1H
                mov.w   #rotation_table,r0
                add.w   r0,r1
                mov.b   @r1,r0L
                mov.b   r0l,@timer_0_const_A

;       If we change rotation then we have to change calabration

set_rotation_done:
                mov.b   @current_config,r0l
                jsr     get_config_ptr
                adds    #2,r0                   ; Skip past enable/
						; disable & antenna
		mov.b	@current_rotation_rate,r1l
		mov.b	#0,r1h
                add.w   r0,r1
                mov.b   @r1,r0l
                mov.b   r0l,@calibration
                rts
;
; ---------------------------------------------------------
;
;       Set up the antenna table based on the argument passed in r1l
;       A side effect is to place this value in memory.

set_antenna_configuration:
                mov.b   r1l,@antenna_configuration
                mov.b   r1l,r0l
                jsr     util_set_antenna_config

                and     #h'f0,r1l
;                cmp.b   #h'30,r1l

set_antenna_4:
                cmp.b   #h'40,r1l
                bne     set_antenna_6
                mov.w   #antenna_4_isr,r5
                bra     set_antenna_exit
;
set_antenna_6:
                cmp.b   #h'60,r1l
                bne     set_antenna_8
                mov.w   #antenna_6_isr,r5
                bra     set_antenna_exit

set_antenna_8:
                cmp.b   #h'80,r1l
                bne     set_antenna_default
                mov.w   #antenna_8_isr,r5
                bra     set_antenna_exit

set_antenna_default:
                mov.w   #str_antenna_bad_count,r1
                jsr     @@writeln_buffered_str
                jsr     util_get_antenna_config
                mov.b   r0l,r1l
                jsr     @@write_byte
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str

                mov.b   #h'40,r0l
                jsr     util_set_antenna_config
                mov.w   @antenna_4_isr,r5

set_antenna_exit:
;		rts
		
;    Fall thru to 
qsync_buffer_start:
			;  205hz	= 20	timer_0_const 60
			; 1137Hz	= 113	timer_0_const 10
			;  Set qsync_bucket_SIZE Should be 100 mS long
			;  at one entry per ant 1			
                push    r1

;       Set qsync_bucket_SIZE Should be 100 mS long
;       at one entry per ant 1 Max size 114 min 19

                mov.w   #1140,r0
                mov.b   @timer_0_const_A,r1L
                divxu   r1L,r0
                mov.b   #0,r0H
                mov.w   #qsync_bucket_mem_start,r1
                add.w   r1,r0
                mov.w   r0,@qsync_bucket_end
                pop     r1
                rts
;
; ---------------------------------------------------------

;       Routine used to calculate a rotation direction for
;       the pointer, for damping the LED display.
;       Input arguments:				ptr example
;               r1 - Target location			180	 80
;               r2 - Current location (pointer or led)	 20     190
;               r3 - 1/2 # of counts round the circle	100     100
;                       (200 for ptr, 100 for led.)

;       WARNING, WILL ROBINSON:

;               These registers are modified in this routine,
;               this is a SIDE EFFECT!
;
; Return  r0h  CW = 0 | CCW = 1 the shortest direction
;
util_calc_dir_vector:
                cmp.w   r2,r1			; is r1 gt r2 180 - 20  =  160 CCW
                bcs     try_CCW			;              20 - 190 = -170 CW
                sub.w   r2,r1			; 180 - 20 r1 = 160
                mov.b   #CW,r0h			; assume CW
                bra     chk_wrong_way

try_CCW:
                sub.w   r1,r2			; 190 - 80 r1 = 110
                mov.w   r2,r1
                mov.b   #CCW,r0h		; assume CCW

chk_wrong_way:

;       r0h has direction
;       r1  has the distance to travel.
;       If the distance to go is more than 1/2 the
;       whole circle, go the other way.

                cmp.w   r3,r1
                bcs     util_calc_dir_exit
;       Take the shorter path

                cmp.b   #CW,r0h
                beq     set_other_direction
                mov.b   #CW,r0h
                bra     util_calc_dir_exit
set_other_direction:
                mov.b   #CCW,r0h

util_calc_dir_exit:
                rts

; ---------------------------------------------------------

;       Reset the 7 segment display structures.
;       This is used in a couple of places to remove any display.

util_seg7_clear:
                mov.b   #h'ff,r0l
                mov.b   r0l,@led_7_marquee_length
                mov.w   #0,r0
                mov.w   r0,@rt_msec_marquee
                rts

; ---------------------------------------------------------

;       Given a configuration id (1-4) in R0L, return the actual
;       address of the configration set in R0.
;


get_config_ptr:
	push	r1
	mov.b	r0l,r1l
	mov.w	#config_1,r0
	dec	r1l
	beq	config_ptr_exit
	mov.w	#config_2,r0
	dec	r1l
	beq	config_ptr_exit
	mov.w	#config_3,r0
	dec	r1l
	beq	config_ptr_exit
	mov.w	#config_4,r0

config_ptr_exit:
	pop	r1
	rts


util_set_active_configuration:

;       Enter with r0L = config number
;       Turn off working config
;       Turn on new config

                push    r1
                push    r2

;       Set the current config variable

                mov.b   r0l,r2l                 ; why Save for later?
                mov.b   r0l,@current_config

;       Set the config bits in the config itself

                mov.b   #1,r1l
util_set_active_loop:
                mov.b   r1l,r0l
                jsr     get_config_ptr

                mov.b   @r0,r2h
                and     #h'0f,r2h               ; turn off
                cmp.b   r1l,r2l
                bne     util_set_active_next
                or      #h'10,r2h
util_set_active_next:
                mov.b   r2h,@r0

                adds    #1,r1
                cmp.b   #ROTATION_RATES + 1,r1l
                bne     util_set_active_loop

;       Probably changed the antenna config, must set it.
                jsr     util_get_antenna_config
                mov.b   r0l,r1l
                jsr     set_antenna_configuration

;       Most likely changed calibration, make sure the new rotation
;       caliration is set.

                mov.b   @current_rotation_rate,r1l
                jsr     set_rotation_rate

                pop     r2
                pop     r1
                rts

;       Get antenna configuration from the current config
;       Return  number of ant  - hi or low in r0L

util_get_antenna_config:
                push    r1
                mov.b   @current_config,r0l
                jsr     get_config_ptr
                adds    #1,r0           ; Skip the enable/disable byte
                mov.b   @r0,r1l
                mov.b   r1l,r0l
                pop     r1
                rts

;       Set the antenna configuration from the current config
;       r0l = new antenna config byte
util_set_antenna_config:
                push    r1
                mov.b   r0l,r1l
                mov.b   @current_config,r0l
                jsr     get_config_ptr
                adds    #1,r0           ; Skip the enable/disable byte
                mov.b   r1l,@r0
                pop     r1
                rts

; ---------------------------------------------------------
;
;       Get one of the calibration values (R0L; 0-9) for current config
;
util_get_calibration_config:
                push    r1
                mov.b   r0l,r1l
                mov.b   #0,r1h                  ; word with 1-9 in it
                mov.b   @current_config,r0l
                jsr     get_config_ptr
                adds    #2,r0                   ; Skip past enable/
						; disable & antenna
                add.w   r0,r1
                mov.b   @r1,r0l
                pop     r1
                rts
;
; ---------------------------------------------------------


button_check_antenna:
util_check_antenna:
cmd_check_antenna:

;       Reg used
;       r0      Set timer
;       r1      Change op mode


;       Turn off the antenna switch while we check

                mov.b   #1,r1L
                mov.b   r1L,@ctrl_byte_hold


;       Turn off led driver too
;       Turn on led driver
                mov.b   #1,r1L
                mov.b   r1L,@ctrl_byte_stop_leds


;       From Qual measurements
ant_chk_qual_done:
                btst    #ANALOG_START_BIT5,@analog_csr
;               bne     ant_chk_qual_done

;       Wait to make sure the hold is on

                mov.w   #ANTENNA_CHECK_WAIT_250,r0
                mov.w   r0,@rt_msec_ant_chk

;       Init LED table (mux driver) and antenna driver table
;       find max number of ants

;       Reg used
;       r0L     Ant address
;       r1L     MUX address

;       Set pointer to first ant

                mov.w   #1,r2
                mov.w   r2,@ant_chk_pointer

;       Don't have to do any math, we want the first one.

                mov.b   @ant_chk_MUX_map,R1L

;       Write mapped MUX control bits to LED port

                mov.b   r1l,@led_port

;       Turn on ant 1

                mov.b   #1,r0L                  ; init
                mov.b   R0L,@tenna_port

;       all set-up for first read

                rts

;       The MUX 74HC4051 is controled by the lower 3 bits of
;       the LED driver.
;       The connection to the ant driver pins could not be done
;       in the correct order (circuit board layout complexity).
;       So they are mapped.

ant_chk_MUX_map:

;       Sets mux enable (low) bit 6 of LED port

                .data.b  4      ; 1
                .data.b  6      ; 2
                .data.b  7      ; 3
                .data.b  5      ; 4
                .data.b  3      ; 5
                .data.b  0      ; 6
                .data.b  1      ; 7
                .data.b  2      ; 8

;       Start the conversion


;       Wait for end of conversion
;       A to D about 15 uS

;       Registers used
;       r0      Pointer to status
;       r0 + 8  Pointer to voltage readings
;       r1L     Temp
;       r1H     voltage at ant
;       r2      Ant chk pointer

ant_chk_adc_read:

;       Crear end flag

                bclr    #ANALOG_FINISH_BIT7,@analog_csr

;       Start conversion

                mov.b   #ANALOG_START_7,r0l
                mov.b   r0l,@analog_csr

ant_chk_adc_wait_finish:
                btst    #ANALOG_FINISH_BIT7,@analog_csr

;       set to 1 when conversion done
;       This will take 122 t states or 153 uS

                beq     ant_chk_adc_wait_finish

                bclr    #ANALOG_FINISH_BIT7,@analog_csr

;       Ready for next A to D conversion

                mov.w   #ant_chk_volts,r0
                mov.w   @ant_chk_pointer,r2
                add.w   r2,r0
                mov.b   @analog_channel_port_3_7,r1H
                mov.b   r1H,@(7,r0)             ; store voltage

;       Test if we have ant 8 data yet

                cmp.b   # 8,r2L
                beq     ant_chk_scan_done

;       Set ant output port

                mov.b   #1,r1L

ant_chk_number:
                shal    R1L
                dec     R2L
                bne     ant_chk_number
ant_chk_got_ant:
                mov.b   R1L,@tenna_port
ant_chk_set_MUX:
                mov.w   #ant_chk_MUX_map,r0
                mov.w   @ant_chk_pointer,r2

                add.w   r2,r0
                inc     r2L
                mov.w   r2,@ant_chk_pointer

;       Set-up for next test

                mov.b   @r0,r1L

;       got MUX ctrl address

                mov.b   r1l,@led_port

                mov.w   #ANTENNA_CHECK_WAIT_250,r0
                mov.w   r0,@rt_msec_ant_chk

                rts

ant_chk_scan_done:

;       Turn on led driver
                mov.b   #0,r1L
                mov.b   r1L,@ctrl_byte_stop_leds


;       Register use
;       r0      Pointer to status
;       r0 + 8  Pointer to voltage readings
;       r1L     counter
;       r1H     voltage at ant
;       r2L     min voltage limit
;       r2H     MAX voltage limit


;       Compare with other antennas
;       Now have all 8 voltage readings

;       Test for HIGH and LOW

                mov.w   #ant_chk_volts,r0
                mov.b   #8,r1L
                mov.b   @antenna_voltage_too_low_d15,r2L        ; 15    0.2 Volts
                mov.b   @antenna_voltage_too_high_d244,r2H      ; 244   4.8 volts

ant_chk_min_max_loop:

                mov.b   @(8,r0),r1H

;       Do the tests
;                      -min ant
                cmp.b   r2L,r1H                 ; if carry set it's below min
                bcc     ant_chk_max

;       It's below min

                mov.b   #1,r1H
                mov.b   r1H,@R0
                bra     ant_chk_next_min_max

ant_chk_max:
;                      -ant max
                cmp.b   r1H,r2H                 ; if carry set it's above max
                bcc     ant_chk_inbounds

                mov.b   #2,r1H
                mov.b   r1H,@R0
                bra     ant_chk_next_min_max

ant_chk_inbounds:
                mov.b   #0,r1H
                mov.b   r1H,@R0

ant_chk_next_min_max:
                adds    #1,r0
                dec     r1L
                bne     ant_chk_min_max_loop




ant_chk_ant_to_ant:

                mov.w   #ant_chk_volts,r0

;       Assume ant 1 as standard to test with
;       Test all ant to ant 1

                mov.b   @r0,r1l                 ; Is it in range?
                bne     ant_chk_ant1_bad

                mov.b   @(8,r0),r2L             ; Standard
                mov.b   @antenna_voltage_same_delta_d14,r1H
                mov.b   r2L,r2H
                sub.b   r1H,r2L                 ; low  boundry
                add.b   r1H,r2H                 ; high boundry
                mov.b   #7,r1L

ant_chk_same_loop:
                adds    #1,r0                   ; get next one
                mov.b   @(8,r0),r1H

                cmp.b   r2L,r1H
                bcs     ant_chk_diff
                cmp.b   r1H,r2H
                bcc     ant_chk_same
ant_chk_diff:
                bset    #2,@r0                  ; not the same
ant_chk_same:
                dec     r1L
                bne     ant_chk_same_loop

ant_chk_ant1_bad:

;       We now have all the info on the ant condition

;       status  byte @ant_chk_volts + ant #
;       bit 2           bit 1           bit 0
;       Not same        Too High        Too Low

;       Voltage reading raw @ant_chk_volts + 8 + ant #

;       The first 3 MUST be ant
;       last ant + 1 stored @ant_chk_last_active




;----------------------------------------------------------

;       We will assume that all ant are good and check for
;       that condition first.
;       No active ant should be high or low or not the "same".
;       Any unused ant should not be low or the "same"

;       'G' = Good      'L' = Low or shorted to ground
;       'H' = Open      'C' = Connected to an ant past last

;       for banner
;       no display of good      format AE#_

;                       'L' = Low or shorted to ground
;       'o' = Open      'c' = Connected to an ant past last

;       If all good banner AC#(H or L)

;       status  byte @ant_chk_volts + ant #
;       bit 2           bit 1           bit 0
;       Not same        Too High        Too Low

;----------------------------------------------------------

;       Get antenna count
                mov.b   @antenna_configuration,r2l
                shlr    r2l
                shlr    r2l     ; move high nibble to
                shlr    r2l     ; the low nibble
                shlr    r2l
                inc     r2l
                mov.w   #ant_chk_volts,r0

ant_chk_active_loop:
                dec     r2L
                beq     ant_chk_active_done

                bset    #3,@r0          ; Ant n
                adds    #1,r0
                bra     ant_chk_active_loop

ant_chk_string_table:

;       bit 3           bit 2           bit 1           bit 0
;       Active          Not same        Too high        Too low

                .data.w str_ant_chk_Extra       ; 0000
                .data.w str_ant_chk_Low         ; 0001
                .data.w str_ant_chk_ok          ; 0010
                .data.w str_ant_chk_D_know      ; 0011

                .data.w str_ant_chk_Ok          ; 0100
                .data.w str_ant_chk_Low         ; 0101
                .data.w str_ant_chk_Ok          ; 0110
                .data.w str_ant_chk_D_know      ; 0111

                .data.w str_ant_chk_active      ; 1000
                .data.w str_ant_chk_D_know      ; 1001
                .data.w str_ant_chk_Open_E      ; 1010
                .data.w str_ant_chk_D_know      ; 1011

                .data.w str_ant_chk_Not_same    ; 1100
                .data.w str_ant_chk_Low         ; 1101
                .data.w str_ant_chk_Open_E      ; 1110
                .data.w str_ant_chk_D_know      ; 1111

ant_chk_error_table:
                .data.b 1       ;ant_chk_Extra           0000
                .data.b 1       ;ant_chk_Low             0001
                .data.b 0       ;ant_chk_ok              0010
                .data.b 0       ;ant_chk_D_know          0011

                .data.b 0       ;ant_chk_Ok              0100
                .data.b 1       ;ant_chk_Low             0101
                .data.b 0       ;ant_chk_Ok              0110
                .data.b 0       ;ant_chk_D_know          0111

                .data.b 0       ;ant_chk_active          1000
                .data.b 0       ;ant_chk_D_know          1001
                .data.b 1       ;ant_chk_Open_E          1010
                .data.b 0       ;ant_chk_D_know          1011

                .data.b 1       ;ant_chk_Not_same        1100
                .data.b 1       ;ant_chk_Low             1101
                .data.b 1       ;ant_chk_Open_E          1110
                .data.b 0       ;ant_chk_D_know          1111

;str_ant_chk_Open_E:
;               .sdataz "Open ERROR"
;str_ant_chk_Ok:
;               .sdataz "Ok"
;str_ant_chk_Low:
;               .sdataz "Low or Shorted"
;str_ant_chk_active:
;               .sdataz "Active"

;str_ant_chk_D_know:
;               .sdataz "Don't Know"
;str_ant_chk_Extra:
;               .sdataz "Too many Antennas"
;str_ant_chk_Not_same:
;               .sdataz "Diode drops don't match"

;str_ant_chk_broken:
;               .sdata  "\n\r*******************\n\r"
;               .sdataz     " VOLTAGE ANTENNA CONDITION"
;str_ant_chk_space:
;               .sdataz "\n\r     "
;str_ant_chk_space2:
;               .sdataz             "     "

ant_chk_active_done:

                mov.w   #str_ant_chk_broken,r1
                jsr     @@write_buffered_str
                mov.b   #0,r3L
                mov.b   r3L,@antenna_failure    ; assume all good
                inc     r3L                     ; ant counter
                mov.w   #ant_chk_volts,r0

ant_chk_print_loop:
                mov.w   #str_ant_chk_space,r1
                jsr     @@write_buffered_str

                push    r0
                mov.b   @(8,r0),r0L
                jsr     util_write_check_voltage
                pop     r0

                mov.w   #str_ant_chk_space2,r1
                jsr     @@write_buffered_str

                mov.b   r3L,r1L
                jsr     write_0toF

                mov.w   #str_ant_chk_space2,r1
                jsr     @@write_buffered_str

                mov.b   @r0,r1L                 ; got status of ant
                mov.b   #0,r1H
                mov.b   @antenna_failure,r2L
                bne     ant_chk_have_error

;       Look for error

                mov.w   #ant_chk_error_table,r2 ; bytes
                add.w   r1,r2
                mov.b   @r2,r2L
                beq     ant_chk_have_error      ; not yet
                mov.b   r3L,@antenna_failure    ; now we do

ant_chk_have_error:
                shal    r1L
                mov.w   #ant_chk_string_table,r2        ; words
                add.w   r1,r2
                mov.w   @r2,r1
                jsr     @@write_buffered_str

                adds    #1,r0
                inc     r3L
                cmp.b   #9,r3L
                bne     ant_chk_print_loop




                mov.w   #str_ant_chk_broken2,r1
                jsr     @@write_buffered_str

;str_ant_chk_broken2:
;               .sdataz "\n\r*******************\n\r"


util_check_antenna_exit:

;       Turn on the antenna switch while we check

                mov.b   #0,r0L
                mov.b   r0L,@ctrl_byte_hold

;       Restart the analog conversion for p_analog process

                mov.b   #ANALOG_START_0,r0l
                mov.b   r0l,@analog_csr


                mov.w   #str_prompt,r1
                jsr     @@write_buffered_str

;       Runs high/low based on argument from check_antenna
                jsr     init_tone

                jmp     init_show_antenna_config


;----------------------------------------------------------

;       Write voltage from the A/D converter.

;       Raw ADC counts in r0l, r0h == do not care
;       Normalize and print the voltage from the
;       ADC to  0 to 5 Volts

;----------------------------------------------------------

util_write_check_voltage:
                push    r1
                push    r2
                push    r3

;       Normalize
                mov.b   #50,r1l
                mulxu   r1l,r0

                mov.b   #255,r1l
                divxu   r1l,r0

;       Print string

;       Peel out Volts
                mov.b   #10,r1l
                mov.b   #0,r0h
                divxu   r1l,r0          ; R0l = Volts, r0h = tenths

                mov.b   r0h,r2l         ; Save from being clobbered
                mov.b   #0,r0h

                mov.w   r0,r1
                jsr     @@write_dec_word

                mov.b   #  '.'  ,r1l
                jsr     @@write_buffered_char

                mov.b   r2l,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word

;       Peel out tenths of a Volt
                pop     r3
                pop     r2
                pop     r1
                rts

;        Read a check voltage from the input buffer.
;        Buffer pointed to by R1
;        Return raw counts in R0
;        Carry Set == error
;        Carry Clear == no error
;        Side effect, modify R1 to point to the first character
;        AFTER the voltage string.
;
;        Legal Strings are:
;               #               5
;               #.              3.
;               #.#             2.1

;        Counts = (voltage*10) * 255 / 50
;        Example
;            (4.7V * 10) * 255 / 50 = 244 counts.

;        Legal input range is 0.0 to 5.0 volts

util_read_check_voltage:
                push    r2
                push    r3
                mov.w   #0,r3

;       Convert first character
                mov.b   @r1,r0l
                mov.b   #  '0'  ,r2l
                sub.b   r2l,r0l
                blt     util_read_check_voltage_error
                cmp.b   #5,r0l
                bgt     util_read_check_voltage_error

;       Volts * 10 == tenths of a volt
                mov.b   #10,r2l
                mulxu   r2l,r0
                mov.b   r0l,r3h

;       Convert "."
                adds    #1,r1
                mov.b   @r1,r2l
                cmp.b   #  '.'  ,r2l
                beq     util_read_check_voltage_tenths
                cmp.b   #  ' '  ,r2l
                ble     util_read_check_voltage_exit

;       Convert tenths
util_read_check_voltage_tenths:
                adds    #1,r1
                mov.b   @r1,r0l

                cmp.b   #  ' '  ,r0l
                ble     util_read_check_voltage_exit

                mov.b   #  '0'  ,r2l
                sub.b   r2l,r0l
                blt     util_read_check_voltage_error
                cmp.b   #9,r0l
                bgt     util_read_check_voltage_error
                mov.b   r0l,r3l

util_read_check_voltage_exit:
                adds    #1,r1

;       Volts + tenths
                add     r3h,r3l

;       tenths * 255
                mov.b   #255,r2l
                mulxu   r2l,r3

;       divided by 50
                mov.b   #50,r2l
                divxu   r2l,r3

;       Lose the remainder and round off
                mov.b   #0,r3h
                mov.w   #5,r0
                add.w   r3,r0

;       Convert the value in r0 (tenths of a volt) to counts
                pop     r3
                pop     r2
                orc     #h'04,ccr       ; Mark the value as good.
                rts

util_read_check_voltage_error:
                mov.w   #str_bad_number,r1
                jsr     @@writeln_buffered_str
                andc    #h'fb,ccr       ; Mark the value as bad
                pop     r3
                pop     r2
                rts

; ---------------------------------------------------------

fence_util_end:

; ---------------------------------------------------------

fence_button_start:

;       Button functions.


;       Send a bearing line to the connected computer.

button_bearing:
;       If we are streaming & GPS comming in, set pending.
;       If we are NOT STREAMING, can print now

                mov.b   #SEG_PAT_B,r1l
                jsr     seg7_force_display
;
button_bearing_write_now:
                jsr     util_write_bearing
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str
;                
; Removed stuff see Removed from line 6907
;
;       Turn on the attract mode.
;       This will stop the led driver and run
;       the attract process, and vice versa.

button_attract:
                mov.b   #PROCESS_STOPPED,r2l
                mov.b   #PROCESS_RUNNING,r2h

                mov.b   @ps_led_driver,r1l
                bne     b4_turn_on_attract

                mov.b   r2l,@ps_attractor
                mov.b   r2h,@ps_led_driver
                bra     button_attract_done

b4_turn_on_attract:
                mov.b   r2h,@ps_attractor
                mov.b   r2l,@ps_led_driver

button_attract_done:
                rts

;       Calibrate the doppler function.
;       It does this by starting the calibration process.

button_calibrate:

;       Clear any interfering modes that may be turned on.

                mov.b   #0,r0H
                mov.b   r0H,@ctrl_byte_hold
                mov.b   r0H,@ctrl_byte_PTT



                mov.b   #1,r0l
                mov.b   r0l,@ps_calibrate

                mov.w   #CALIBRATION_WAIT_VALUE,r0
                mov.w   r0,@calibration_timer

                mov.b   #0,r1l
                jsr     set_rotation_rate

                mov.w   @maintenance_mode,r0
                bset    #MODE_MAINT_CALIBRATE_BV,r0l
                mov.w   r0,@maintenance_mode
                rts

; ---------------------------------------------------------

;       Switch between one of four configurations.
;       When a new config is set, display "c#"
;       If a configuration is disabled, display "cE#"

button_config:
                mov.b   @current_config,r0l
                add.b   #1,r0l
                cmp.b   #5,r0l
                bne     button_config_set_next
;       wrap around if it is 5 make it a 1
                mov.b   #1,r0l

;       Enter with r0L = config number

button_config_set_next:
                jsr     util_set_active_configuration

                mov.b   @current_config,r0l
                jsr     get_config_ptr
                mov.b   @r0,r1l
                and     #h'0f,r1l
                beq     button_config_show_error

button_config_show:
                mov.b   #SEG_PAT_LOW_C,r1h
                mov.b   @current_config,r1l
                jmp     seg7_force_2display
;       jsr     seg7_force_2display
;       rts

button_config_show_error:
                mov.w   #led_7_marquee,r0
;       "c"
                mov.b   #SEG_PAT_LOW_C,r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       "E"
                mov.b   #SEG_PAT_E,r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       "#"
                mov.b   @current_config,r1l
                mov.b   r1l,@r0
                adds    #1,r0
;       Finish up
                mov.b   #3,r0l
                mov.b   r0l,@led_7_marquee_length
                mov.b   #0,r0l
                mov.b   r0l,@led_7_marquee_idx
                rts

; ---------------------------------------------------------



;button_gps:
;;       If capture string is no good, don't bother
;                mov.w   @rt_sec_gps,r0
;                beq     button_gps_exit
;
;;       If we are streaming & GPS comming in, set pending.
;;       If we are NOT STREAMING, can print now
;
;                mov.b   #SEG_PAT_G,r1l
;                jsr     seg7_force_display
;
;                mov.b   @GPS_echo_flag,r1L
;                beq     button_gps_write_now
;
;
;                mov.b   @GPS_capture_flag,r1L
;                beq     button_gps_write_now
;
;;       Queue up a request for later
;                mov.b   #1,r0L
;                mov.b   r1L,@GPS_capture_flag_SNOOP_PENDING
;                bra     button_gps_exit
;
;button_gps_write_now:
;;????                mov.w   #gps_valid_capture,r1
;                mov.b   @r1,r0l
;                beq     button_gps_exit
;;????                mov.w   #gps_valid_capture,r1
;                jsr     @@write_buffered_str
;                mov.b   #LF,r1l
;                jsr     @@write_buffered_char
;
;button_gps_exit:
;                rts
                
button_ptrf:
                mov.b   @current_ptr_filter,r0l
                inc     r0L
                cmp.b   #max_filter/2-1,r0l                ; Last filter
                bls     button_ptr_filter_in_range
                mov.b   #0,r0l                          ; set ptrf to 0

button_ptr_filter_in_range:
;
;                          Have a filter number 0 - last filter
;                          Make it ready to point to word table
;                          If it is absolute add in offset
;                          get address of first filter data
;                          put it at data_4_ptr

                mov.b   r0l,@current_ptr_filter   ; Number 0 - last filter
                mov.b   #0,r0h                    ; make it 16 bit
                shal    r0l                       ; table is word
                mov.b   @pointer_abs_flag,r1l     ; rel = 0 abs = 1
                mov.b   #0,r1h                    ; Make it 16 bit
                add.w   r1,r0                     ; offset for filter - a/r
                mov.w   #filt_0_output,r1         ; address of first filter
                add.w   r0,r1                     ; address of selected filter
                                                  ; filter output data address
                mov.w   #data_4_ptr,r0
                mov.w   r1,@r0
                mov.b   @current_ptr_filter,r1l
                mov.b   #SEG_PAT_P,r1h
                jmp     seg7_force_2display

button_ptra:                        
                mov.b   @pointer_abs_flag,r0l
                beq	button_pointer_make_A
button_pointer_make_R:                
                mov.b   #0,r0l
                mov.b   r0l,@pointer_abs_flag
                jsr	update_data_4_pointer
                mov.b   #SEG_PAT_P,r1h
                mov.b	#SEG_PAT_LOW_R,r1l
                jmp     seg7_force_2display
;
button_pointer_make_A:
		mov.b   #max_filter,r0l
		mov.b   r0l,@pointer_abs_flag
		jsr	update_data_4_pointer
		mov.b   #SEG_PAT_P,r1h
                mov.b	#SEG_PAT_A,r1l
                jmp     seg7_force_2display
;
;display_address_table:
;
;       Which filter output is used by which display
;       filter output data address 0 to ?data in table.
;
; F964" 	.data.w data_4_leds     ; Data address 4 leds
; F966" 	.data.w data_4_ptr      ; load with filt_x_output
; F968" 	.data.w data_4_lcda	; lcd absolute bearing
; F96A" 	.data.w data_4_lcdr	; lcd relative bearing
; F96C" 	.data.w data_4_serial
; F96E" 	.data.w data_4_lrtone
		
; 00F970	current_led_filter:             .res.b  1
; 00F971	current_ptr_filter:             .res.b  1
; 00F972	current_lcda_filter:		.res.b	1
; 00F973	current_lcdr_filter:		.res.b	1
; 00F974	current_serial_filter:		.res.b	1
; 00F975	current_lrtone_filter:		.res.b	1
                

;
; F7A2		filt_0_output:                  .res.w  1
; F7A4		filt_1_output:                  .res.w  1
; F7A6		filt_2_output:                  .res.w  1
; F7A8		filt_3_output:                  .res.w  1
; F7AA		filt_4_output:			.res.w	1
; 		filt_5_output			.res.w	1
;
; F7AC		filt_0_A_output:                .res.w  1
; F7AE		filt_1_A_output:                .res.w  1
; F7B0		filt_2_A_output:                .res.w  1
; F7B2		filt_3_A_output:                .res.w  1
; F7B4		filt_4_A_output:                .res.w  1
;		filt_5_A_output:                .res.w  1
;     
update_data_4_pointer:

		mov.b   @current_ptr_filter,r0l                
		mov.b   #0,r0h
                shal    r0l				; table is word
                mov.b   @pointer_abs_flag,r1l           ; rel = 0 abs = 2 times max filters
                mov.b   #0,r1h
                add.w   r1,r0
                mov.w   #filt_0_output,r1
                add.w   r0,r1                           ; filter output data address
                mov.w   #data_4_ptr,r0
                mov.w   r1,@r0				; trouble in here
		rts               
;
button_ledf:
                mov.b   @current_LED_filter,r0l
                inc     r0L
                cmp.b   #max_filter/2,r0l		; Last filter
                bls     button_LED_filter_in_range
                mov.b   #0,r0l                          ; set ledf to 0

button_led_filter_in_range:
;
;                          Have a filter number 0 - last filter
;                          Make it ready to point to word table
;                          If it is absolute add in offset
;                          get address of first filter data
;                          put it at data_4_ptr
;
                mov.b   r0l,@current_led_filter
                mov.b   #0,r0h
                shal    r0l				; table is word
                mov.b   @LED_abs_flag,r1l               ; rel = 0 abs = 2 times max filters
                mov.b   #0,r1h
                add.w   r1,r0
                mov.w   #filt_0_output,r1
                add.w   r0,r1                           ; filter output data address
                mov.w   #data_4_leds,r0
                mov.w   r1,@r0
                mov.b   @current_led_filter,r1l
                mov.b   #SEG_PAT_L,r1h
                jmp     seg7_force_2display
;                
button_leda:            
                mov.b   @LED_abs_flag,r0l
                beq	button_leda_make_A
button_leda_make_R                
                mov.b   #0,r0l
                mov.b   r0l,@LED_abs_flag
                jsr	update_data_4_leds
                mov.b   #SEG_PAT_L,r1h
                mov.b	#SEG_PAT_LOW_R,r1l
                jmp     seg7_force_2display
;
;
button_leda_make_A:
		mov.b   #max_filter,r0l
		mov.b   r0l,@LED_abs_flag
		jsr	update_data_4_leds
		mov.b   #SEG_PAT_L,r1h
                mov.b	#SEG_PAT_A,r1l
                
                jmp     seg7_force_2display
                
update_data_4_leds:
		mov.b   @current_led_filter,r0l                
		mov.b   #0,r0h
                shal    r0l				; table is word
                mov.b   @LED_abs_flag,r1l               ; rel = 0 abs = 2 times max filters
                mov.b   #0,r1h
                add.w   r1,r0
                mov.w   #filt_0_output,r1
                add.w   r0,r1                           ; filter output data address
                mov.w   #data_4_leds,r0
                mov.w   r1,@r0
		rts
;
button_lcda:
                mov.b   @current_lcda_filter,r0l
                inc     r0L
                cmp.b   #max_filter/2-1,r0l                ; Last filter
                bls     button_lcda_filter_in_range
                mov.b   #0,r0l                          ; set ledf to 0

button_lcda_filter_in_range:
;
;                          Have a filter number 0 - last filter
;                          Make it ready to point to word table
;                          If it is absolute add in offset
;                          get address of first filter data
;                          put it at data_4_ptr
;
                mov.b   r0l,@current_lcda_filter
                mov.b   #0,r0h
                shal    r0l				; table is word
                mov.w   #filt_0_A_output,r1
                add.w   r0,r1                           ; filter output data address
                mov.w   #data_4_lcda,r0
                mov.w   r1,@r0
                mov.b   @current_lcda_filter,r0l
                or	#'0',r0l
                mov.b	r0l,@lcd_afilt
                rts
;
button_lcdr:
                mov.b   @current_lcdr_filter,r0l
                inc     r0L
                cmp.b   #max_filter/2-1,r0l                ; Last filter
                bls     button_lcdr_filter_in_range
                mov.b   #0,r0l                          ; set ledf to 0

button_lcdr_filter_in_range:
;
;                          Have a filter number 0 - last filter
;                          Make it ready to point to word table
;                          If it is absolute add in offset
;                          get address of first filter data
;                          put it at data_4_ptr
;
                mov.b   r0l,@current_lcdr_filter
                mov.b   #0,r0h
                shal    r0l				; table is word
                mov.w   #filt_0_output,r1
                add.w   r0,r1                           ; filter output data address
                mov.w   #data_4_lcdr,r0
                mov.w   r1,@r0
                mov.b   @current_lcdr_filter,r0l
                or	#'0',r0l
                mov.b	r0l,@lcd_afilt
                rts		
		
button_dim:
                mov.w   #ctrl_byte_Dim_LED,r0
                bxor    #0,@r0
                rts
;
;	Change the rotation rate of the antennas.
;	This happens in sequence.
;	Rate # is displayed on the 7 segment display.

button_rot:
		mov.b	@current_rotation_rate,r0l
		add.b	#1,r0l
		mov.b	#9,r0h
		cmp.b	r0h,r0l
		bls	button_rate_in_range
		mov.b	#0,r0l

button_rate_in_range:
		mov.b	r0l,r1l
		jsr	set_rotation_rate
		mov.b	@current_rotation_rate,r1l
		mov.b	#SEG_PAT_LOW_R,r1h
		jmp	seg7_force_2display
;               
;       Change threshold.
;       This happens in sequence.
;       # is displayed on the 7 segment display.

button_threshold:
                mov.b   @current_Threshold,r1l
                inc     r1L
                cmp.b   #5,r1l
                bls     threshold_in_range
                mov.b   #1,r1l          	; set threshold to 1
;
threshold_in_range:
                mov.b	r1l,@current_Threshold
                mov.b   #SEG_PAT_LOW_0_DOT,r1h
                jmp     seg7_force_2display
;                             
button_sample_size:
                mov.b   @current_sample_number,r1l
                inc     r1L
                cmp.b   #5,r1l
                bls     sample_in_range
                mov.b   #1,r1l          	; set sample size to 1
;
sample_in_range:
		mov.b	r1l,@current_sample_number
		mov.b	#48,r0l			; size of (1)sample
		mulxu	r1l,r0			; 48, 96, 144, 192, 240
                mov.b	r0l,@current_sample_size
                mov.b   #SEG_PAT_5_DOT,r1h
                jmp     seg7_force_2display
;       Turn snooping on and off.

;button_snooper:
;                mov.b   @ps_aprs_snooper,r0l
;                beq     button_snooper_on
;                mov.b   #0,r0l          ; flag false
;                mov.b   r0l,@ps_aprs_snooper
;                rts
;
;button_snooper_on:
;                mov.b   #1,r0l          ; flag true
;                mov.b   r0l,@ps_aprs_snooper
;                rts

;       Pointer speed control function

button_pointer:
                mov.b   @pointer_delay_idx,r1l
                adds    #1,r1
                cmp.b   #POINTER_DELAY_IDX_MAX,r1l
                bls     button_pointer_set
                mov.b   #POINTER_DELAY_IDX_MIN,r1l

button_pointer_set:
                jsr     util_set_pointer_delay
                mov.b   #SEG_PAT_P,r1h
                mov.b   @pointer_delay_idx,r1l
                adds    #1,r1                   ; Display values of 1 - 5
                jmp     seg7_force_2display


;       LED speed control function
button_led_speed:
                mov.b   @current_LED_speed,r1l
                inc 	r1l
                cmp.b   #LED_speed_MAX,r1l
                bls     button_led_set
                mov.b   #LED_speed_MIN,r1l
button_led_set:
		mov.b	r1l,@current_LED_speed
                jsr     util_set_led_delay
                mov.b   #SEG_PAT_L,r1h
                mov.b   @current_LED_speed,r1l               
                jmp     seg7_force_2display


;       Turn the pointer on and off.

button_ptr_on_off:
                mov.b   @ps_stepper_driver,r0l
                beq     button_ptr_oo_on
                mov.b   #0,r0l          	; flag false
                mov.b   r0l,@ps_stepper_driver
                mov.b   #0,r1l
                mov.b   r1l,@h'ffc1
                rts

button_ptr_oo_on:
                mov.b   #1,r0l          	; flag true
                mov.b   r0l,@ps_stepper_driver
                rts

;       Set or clear the bit to hold the LED display.

button_hold:

                mov.b   @ctrl_byte_hold,r0l
                beq	make_hold_1
                mov.b	#0,r0l
                bra	save_hold
make_hold_1:
		
		mov.b   #SEG_PAT_H,r1l
                jsr     seg7_force_display
                mov.b	#1,r0l
save_hold:                
                mov.b   r0l,@ctrl_byte_hold
                rts

button_save:
                jsr     cmd_eeprom_save

                mov.b   #SEG_PAT_S,r1h
                mov.b   #SEG_PAT_A,r1l
                jmp     seg7_force_2display

;       Send custom string out serial port, display klingon

button_cust_1:
                mov.w   #bstr_func_1,r1
                jsr     @@writeln_buffered_str
                mov.b   #SEG_PAT_K1,r1l
                jmp     seg7_force_2display

;       Send custom string out serial port, display klingon

button_cust_2:
                mov.w   #bstr_func_2,r1
                jsr     @@writeln_buffered_str
                mov.b   #SEG_PAT_K2,r1l
                jmp     seg7_force_2display

;       Send custom string out serial port, display klingon

button_cust_3:
                mov.w   #bstr_func_3,r1
                jsr     @@writeln_buffered_str
                mov.b   #SEG_PAT_K3,r1l
                jmp     seg7_force_2display

;       Send custom string out serial port, display klingon

button_cust_4:
                mov.w   #bstr_func_4,r1
                jsr     @@writeln_buffered_str
                mov.b   #SEG_PAT_K4,r1l
                jmp     seg7_force_2display

fence_button_end:

fence_eeprom_start:
;			93CS56 128 16 bit word
;			Serial EEPROM
;			 __  __
;	    Port 64 CS 1|  \/  |8 Vcc
;	    Port 63 SK 2|      |7 PRE GND
;	    Port 65 DI 3|      |6 PE  +5
;	    Port 66 DO 4|______|5 GND
;
;                              READ
;     ___________________________________________________________________
;CS__/                                                                   \
;
;         _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   _
;SK______| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_|
;
;        _______
;       / 1   1 \ 0 /A7\ Ax\ A0\
;DI    /         \_/            \__________________________________________
;
;DO__________________________    / \ / \ / \ Keeps reading until cs goes low
;                            \0_/D15 Dx  D0
;
; ***********************************************************************
;
;                              Write Enable
;     ___________________________________________________________________
;CS__/                                                                   \
;				11 Clocks required
;         _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   _
;SK______| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_|
;
;        ___         ______
;       / 1 \ 0   0 / 1   1\ XX
;DI    /     \_____/            \__________________________________________
;
; ************************************************************************
;
;                              Write
;     ___________________________________________________________________
;CS__/                                                                   \
;
;         _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   _
;SK______| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_|
;
;        _______
;       / 1   1 \ 0 /A7\ Ax\ A0\/D15/Dx\/D0\
;DI    /         \_/                        \____________________________
;
;
;DO                                             Busy ______
;     -----------------------------------------\____/ Ready\----------
;
; ***********************************************************************
;
;                              Write Disable
;     ___________________________________________________________________
;CS__/                                                                   \
;				11 Clocks required
;         _   _   _   _   _   _   _   _   _   _   _   _   _   _   _   _
;SK______| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_| |_|
;
;        ___         
;       / 1 \ 0   0   0   0   X
;DI    /     \______________/   \__________________________________________
;
;
; ---------------------------------------------------------
;       EEPROM Maintenance Routines
; ---------------------------------------------------------

; MUST! Write Enable before write and eeprom_write_enable
;            Write Disable after write eeprom_write_disable

;       Send a command to the eeprom.
;       Arguments are:
;               cmd  r1h[1:0] commands 2 bits
;               commands 10xx = read
;                          01xx = write
;                          11xx = erase

;               addr r1l[7:0] ($00-$7f) 7 bits of address
;               but you send 8 bits first one is don't care
;               bit 7 is sent first
;       Required for the National Semiconductor NM93CS56

;       Write register value
;       r1l = address of register [7:0] ($00-$7f) and
;       r2 = value to be written

;**********************************************************

;       Read register value
;       r1l = address of register [8:0] ($00-$7f)
;       r0  = Value read from register

;**********************************************************

eeprom_read:

                bset    #4,@port_6              ; chip select
                mov.b   #2,R1H			; eeprom_cmd_read
                jsr     eeprom_cmd

;       Loop through all high byte data bits writing them out.

                push    R2
                mov.b   #16,R1H
eeprom_read_loop:
                bset    #3,@port_6              ; clock

;       see next clock after data is set

;       Test the bit then set carry and shift it in.

                btst    #6,@port_6              ; eeprom_data_out_bit
                  beq   eeprom_set_bit_zero
                orc     #01,ccr                 ; set carry
                  bra   eeprom_shift_it

eeprom_set_bit_zero:
                andc    #h'FE, ccr              ;clear carry

;       Shift in the new bit, from the carry.

eeprom_shift_it:
                rotxl   R2L
                rotxl   R2H

eeprom_read_next_bit:
                bclr    #3,@port_6              ; clock
                dec     R1H
                  bne   eeprom_read_loop

eeprom_read_done:
                bclr    #4,@port_6

;       Make sure the chip sees the deselect.
                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

;       Place EEProm register value into R0

                mov.w   R2, R0
                pop     R2
                rts

eeprom_write:

                bset    #4,@port_6              ; chip select
                mov.b   #01,R1H			; eeprom_cmd_write
                jsr     eeprom_cmd

;       Loop through all data bits writing them out.

                mov.b   #16,R1H
eeprom_write_loop:
                rotxl   R2L             ; get bit to send into carry
                rotxl   R2H
                  bcc    eeprom_write_data_low
                bset    #5,@port_6      ; eeprom_data_in_bit
;       Sent a 1 to eeprom
                  bra    eeprom_write_sent
eeprom_write_data_low:
                bclr    #5,@port_6      ; eeprom_data_in_bit
;       Sent a 0 to eeprom
eeprom_write_sent:
                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock
;       Now clocked in
                dec     R1H
                  bne    eeprom_write_loop

eeprom_write_done:
                bclr    #4,@port_6

;       Wait for chip to be ready.

                bset    #4,@port_6
eeprom_write_wait_for_ready:
                btst    #6,@port_6      ; eeprom_data_out_bit
                  beq    eeprom_write_wait_for_ready

                bclr    #4,@port_6
                rts

; ---------------------------------------------------------

eeprom_cmd:

;       Send the start bit
                bset    #5,@port_6      ; eeprom_data_in_bit
                bset    #3,@port_6      ; clock
                bclr    #3,@port_6      ; clock

;       Send the two command bits
;       The effort require to loop for 2 bits isn't worth it!
;       Bit 1
                btst    #1,R1H

;       find out what the command is

                  beq   eeprom_cmd_low_1
                bset    #5,@port_6      ; eeprom_data_in_bit
                  bra   eeprom_cmd_send_bit_1
eeprom_cmd_low_1:
                bclr    #5,@port_6      ; eeprom_data_in_bit
eeprom_cmd_send_bit_1:
                bset    #3,@port_6      ; clock
                bclr    #3,@port_6      ; clock
;       Bit 0
                btst    #0,R1H
                  beq   eeprom_cmd_low_0
                bset    #5,@port_6      ; eeprom_data_in_bit
                  bra   eeprom_cmd_send_bit_0
eeprom_cmd_low_0:
                bclr    #5,@port_6      ; eeprom_data_in_bit
eeprom_cmd_send_bit_0:
                bset    #3,@port_6      ; clock
                bclr    #3,@port_6      ; clock

;       Send the Address, loop through all bits

                mov.b   #7,R1H          ; send 8 bits of address
eeprom_cmd_address_loop:
                btst    R1H, R1L
                  beq   eeprom_cmd_addr_low
                bset    #5,@port_6      ; eeprom_data_in_bit
                  bra   eeprom_cmd_send_addr
eeprom_cmd_addr_low:
                bclr    #5,@port_6      ; eeprom_data_in_bit
eeprom_cmd_send_addr:
                bset    #3,@port_6      ; clock
                bclr    #3,@port_6      ; clock
                cmp.b   #0, R1H
                  beq   eeprom_cmd_address_done
                mov.b   #1, R0H
                sub.b   R0H, R1H
                  bra   eeprom_cmd_address_loop

eeprom_cmd_address_done:
                rts

;       Write enable the chip.
;       This should be balanced with a call to write disable.

eeprom_write_enable:

;       Write Enable the chip

                push    R1
                bset    #4, @port_6             ; chip select
                mov.b   #0,R1H			; eeprom_cmd_write_enable
                mov.b   #h'0c3,R1L		; eeprom_addr_write_enable
                bra     eeprom_clock


;       Write disable the EEPROM. This should have been
;       preceeded by a call to write enable.

eeprom_write_disable:
                push    R1
                bset    #4,@port_6             ; chip select
                mov.b   #0,R1H			; eeprom_cmd_write_disable
                mov.b   #h'0b,R1L		; eeprom_addr_write_disable

;       falls thru to eeprom_clock
; ---------------------------------------------------------

eeprom_clock:

;       Data sheet claims it needs at least 9 clocks, make sure
;       that it gets at least 11, or more.

                jsr     eeprom_cmd

                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

                bset    #3,@port_6              ; clock
                bclr    #3,@port_6              ; clock

                bclr    #4,@port_6              ; chip select
                pop     R1
                rts
;
cmd_eeprom_save:
                jsr     eeprom_write_enable

;       Write Word value to eeprom

                mov.b   #h'00,r3l		; address
		mov.b   #eeprom_image_size,r3h
		shlr	r3h			; words not bytes
						; End address
                mov.w	#eeprom_ram_start-2,r2
                mov.w	r2,@eesave_ptr
cmd_eeprom_save_loop:
                mov.b   r3l,r1l
                mov.w	@eesave_ptr,r2
                adds	#2,r2
                mov.w	r2,@eesave_ptr
                mov.w   @r2,r2
                jsr     eeprom_write
                inc     r3l

                cmp.b   r3h,r3l
                bne     cmd_eeprom_save_loop

                jmp     eeprom_write_disable
                rts
;                
; ---------------------------------------------------------
;
; Need to load perameters of stuf to set up doppler.
; config, rot, calabration, baud rate, button asignments, +
; Place in external ram for debug
; Place in in chip ram for production
;
eeprom_restore:
;
; See if a button it pressed, it so do not load EEPROM
;
		mov.b	#0,r0l
		mov.b	r0l,@port3_dr
		btst    #6,@button_in_dr       ; read buttons

		bne	eeprom_load_allowed
;		mov.w	#str_eeprom_not_loaded,r1
;		jsr	writeln_buffered_str
		rts
;
eeprom_load_allowed:
                mov.b   #0,r1l			; EEPROM address
                mov.w	#eeprom_ram_start,r2	; Data desintation
cmd_eerestore_read_loop:

                jsr     eeprom_read		; address in r1l
						; ret data in r0
		mov.w	r0,@r2
		adds	#2,r2
		inc	r1l
		cmp.b	#eeprom_image_size/2,r1l
		bne	cmd_eerestore_read_loop	
		rts
;
fence_eeprom_end:

fence_cmd_start:

; ---------------------------------------------------------

;       CLI Command Routines
;       These routines can use all regular registers.

; ---------------------------------------------------------
;
;       Print, or set the audio alarm time.
;       alarm [#sec]

cmd_alarm:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_alarm_show
                jsr     read_dec_word
                mov.w   r0,@lost_alarm_time

cmd_alarm_show:
                mov.w   @lost_alarm_time,r1
                jsr     @@write_dec_word
                mov.w   #str_seconds,r1
                jmp     @@writeln_buffered_str
;       jsr     @@writeln_buffered_str
;       rts

; Print, or set the antenna configuration.

cmd_asw:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.b   @r1,r2l
                bne     cmd_asw_set_config

;       Show the antenna configuration

cmd_asw_show_config:
		jsr	write_current_config

                jmp     util_write_calibrations


cmd_asw_set_config:

;       Remember, antenna tables are 3,4,5,6,8
;       Switch is only 0 or 1

                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.w   r1,r2
                jsr     read_word
                cmp.b   #03,r0l
                beq     cmd_asw_accept
                cmp.b   #04,r0l
                beq     cmd_asw_accept
                cmp.b   #05,r0l
                beq     cmd_asw_accept
                cmp.b   #06,r0l
                beq     cmd_asw_accept
                cmp.b   #08,r0l
                beq     cmd_asw_accept

;       Whoops, illegal number of elements

cmd_asw_abort:
                mov.w   #str_antenna_bad_count,r1
                jsr     @@writeln_buffered_str
                bra     cmd_asw_show_config

cmd_asw_accept:
                shll    r0l
                shll    r0l
                shll    r0l
                shll    r0l
                mov.b   r0l,@temporary
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_asw_abort
                jsr     cmd_skip_token
                bne     cmd_asw_abort
                jsr     cmd_get_boolean_token
                mov.b   @temporary,r0h
                or      r0h,r0l
                mov.b   r0l,r1l
                jsr     set_antenna_configuration

;       All done, feed back to the user.

                mov.w   #cmd_asw_show_config,r0
                jmp     @r0
;----------------------------------------------------------
;
;       Set the baud rate to 1200, 2400, 4800, 9600 or 19200 baud.

cmd_baud:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_baud_show
                jsr	cmd_baud_set
                mov.b	r0l,@serial_rate
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
		jsr     cmd_skip_token
                bne     cmd_baud_show
                jsr	cmd_baud_set

                mov.b	r0l,@serial_rate1
                bne     cmd_baud_show
                rts
cmd_baud_set:
                mov.w   r1,r2
                jsr     read_word

cmd_baud_test_12:
                cmp.b   #h'12,r0l
                beq     cmd_baud_set_12
                mov.w   #h'1200,r1
                cmp.w   r1,r0
                bne     cmd_baud_test_24
cmd_baud_set_12:
                mov.b   #BIT_RATE_1200,r0l
                rts
cmd_baud_test_24:
                cmp.b   #h'24,r0l
                beq     cmd_baud_set_24
                mov.w   #h'2400,r1
                cmp.w   r1,r0
                bne     cmd_baud_test_48
cmd_baud_set_24:
                mov.b   #BIT_RATE_2400,r0l
                rts
cmd_baud_test_48:
                cmp.b   #h'48,r0l
                beq     cmd_baud_set_48
                mov.w   #h'4800,r1
                cmp.w   r1,r0
                bne     cmd_baud_test_96
cmd_baud_set_48:
                mov.b   #BIT_RATE_4800,r0l
                rts
cmd_baud_test_96:
                cmp.b   #h'96,r0l
                beq     cmd_baud_set_96
                mov.w   #h'9600,r1
                cmp.w   r1,r0
                bne     cmd_baud_set_19200
cmd_baud_set_96:
                mov.b   #BIT_RATE_9600,r0l
                rts
cmd_baud_set_19200:
		mov.b	#BIT_RATE_19200,r0l
		rts
cmd_baud_set_done:                              ; XXXX Error
;       rts
;
;----------------------------------------------------------
;
cmd_baud_show:
		mov.w   #uart0_str,r1
                jsr     @@write_buffered_str
                mov.b   @serial_rate,r1l
                jsr	cmd_baud_show_12
cmd_baud_show2:
		mov.w   #uart1_str,r1
                jsr     @@write_buffered_str
                mov.b   @serial_rate1,r1l
cmd_baud_show_12:
                cmp.b   #BIT_RATE_1200,r1l
                bne     cmd_baud_show_24
                mov.b   #h'12,r1l
                jsr     @@write_byte
                bra     cmd_show_done
cmd_baud_show_24:
                cmp.b   #BIT_RATE_2400,r1l
                bne     cmd_baud_show_48
                mov.b   #h'24,r1l
                jsr     @@write_byte
                bra     cmd_show_done
cmd_baud_show_48:
                cmp.b   #BIT_RATE_4800,r1l
                bne     cmd_baud_show_96
                mov.b   #h'48,r1l
                jsr     @@write_byte
                bra     cmd_show_done
cmd_baud_show_96:
                cmp.b   #BIT_RATE_9600,r1l
                bne     cmd_baud_show_19
                mov.b   #h'96,r1l
                jsr     @@write_byte
                bra     cmd_show_done
cmd_baud_show_19:
                cmp.b   #BIT_RATE_19200,r1l
                bne     cmd_baud_show_eh
                mov.b   #h'19,r1l
                jsr     @@write_byte
                mov.b	#2,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                bra     cmd_show_done                
cmd_baud_show_eh:
                mov.w   #str_baud_error,r1
                jmp     @@writeln_buffered_str

cmd_show_done:
                mov.b   #0,r1l
                jsr     @@write_byte
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str
;
;----------------------------------------------------------
;
;       Set the baud rate to 1200, 2400, 4800, 9600 or 19200 baud.
;	of the second uart to send bearing, quality and compass
cmd_baud2:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_baud_show2
cmd_baud2_set:
                mov.w   r1,r2
                jsr     read_word
cmd_baud2_test_12:
                cmp.b   #h'12,r0l
                beq     cmd_baud2_set_12
                mov.w   #h'1200,r1
                cmp.w   r1,r0
                bne     cmd_baud2_test_24
cmd_baud2_set_12:
                mov.b   #BIT_RATE_1200,r0l
                mov.b   r0l,@serial_rate1
                bra     cmd_baud2_set_done
cmd_baud2_test_24:
                cmp.b   #h'24,r0l
                beq     cmd_baud2_set_24
                mov.w   #h'2400,r1
                cmp.w   r1,r0
                bne     cmd_baud2_test_48
cmd_baud2_set_24:
                mov.b   #BIT_RATE_2400,r0l
                mov.b   r0l,@serial_rate1
                bra     cmd_baud2_set_done
cmd_baud2_test_48:
                cmp.b   #h'48,r0l
                beq     cmd_baud2_set_48
                mov.w   #h'4800,r1
                cmp.w   r1,r0
                bne     cmd_baud2_set_96
cmd_baud2_set_48:
                mov.b   #BIT_RATE_4800,r0l
                mov.b   r0l,@serial_rate1
                bra     cmd_baud2_set_done
cmd_baud2_test_96:
                cmp.b   #h'96,r0l
                beq     cmd_baud2_set_96
                mov.w   #h'9600,r1
                cmp.w   r1,r0
                bne     cmd_baud2_set_192
cmd_baud2_set_96:
                mov.b   #BIT_RATE_9600,r0l
                mov.b   r0l,@serial_rate1
                bra     cmd_baud2_set_done
cmd_baud2_set_192:
                mov.b   #BIT_RATE_19200,r0l
                mov.b   r0l,@serial_rate1
cmd_baud2_set_done:                              ; XXXX Error
;       rts
;----------------------------------------------------------
;
; Print, or set the button configuration.
;       btab [B# F#] | -

cmd_btab:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.b   @r1,r2l
                beq     cmd_btab_show_table

;       See if they want to show whole table

                cmp.b   #  '?'  ,r2l
                bne     cmd_btab_set_config
;
cmd_btab_show_full_table:
                mov.w   #button_table,r1
cmd_btab_show_full_loop:
                mov.w   @r1,r0
                mov.w   #h'ffff,r2
                cmp.w   r2,r0
                beq     cmd_btab_show_full_done
                mov.w   #4,r2
                add.w   r2,r1
;       Print the button code
                push    r1
                jsr     @@write_buffered_str
                mov.w   #bstr_separator,r1
                jsr     @@write_buffered_str
                pop     r1
;       And the description string.
                mov.w   #6,r2
                add.w   r2,r1
                push    r1
                mov.w   @r1,r2
                mov.w   r2,r1
                jsr     @@writeln_buffered_str
                pop     r1
                mov.w   #2,r2
                add.w   r2,r1
                bra     cmd_btab_show_full_loop

cmd_btab_show_full_done:
                rts
;
;       show the button function table
;
cmd_btab_show_table:
                mov.w   #str_button_list,r2
                mov.b   #01,r3l
                mov.w   #button_1_function,r4
cmd_btab_show_loop:
;       Write the button number label

                mov.w   @r2+,r1
                jsr     @@write_buffered_str
                mov.b   @r4+,r1l
                push    r2
                jsr     cmd_btab_search
                mov.w   r0,r2
                mov.w   #4,r1
                add.w   r0,r1

;       Write button descriptor

                jsr     @@write_buffered_str
                mov.w   #bstr_separator,r1
                jsr     @@write_buffered_str
                mov.w   #10,r1
                add.w   r1,r2
                mov.w   @r2,r1

;       Write long description string.

                jsr     @@writeln_buffered_str
                pop     r2
                adds    #1,r3
                cmp.b   #16,r3l
                bls     cmd_btab_show_loop

                rts

;       btab [B# F#]
cmd_btab_set_config:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.w   r1,r2
                jsr     read_dec_word
                bne     cmd_btab_illegal_button_no
                mov.w   r0,r3           ; For safe keeping
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                jsr     cmd_btab_fc_search
                cmp.b   #0,r0l
                beq     cmd_btab_illegal_spec

;       Really set the button

                cmp.b   #1,r3l
                blo     cmd_btab_illegal_button_no
                cmp.b   #16,r3l       			; max button #
                bhi     cmd_btab_illegal_button_no
                mov.w   #button_1_function,r1
                mov.b   #0,r3h
                add.w   r3,r1
                subs    #1,r1
                mov.b   r0l,@r1
                rts

cmd_btab_illegal_button_no:
                mov.w   #str_btab_illegal_button_no,r1
                jmp     @@writeln_buffered_str

cmd_btab_illegal_spec:
                mov.w   #str_btab_illegal_spec,r1
                jmp     @@writeln_buffered_str

;       This routine will search the button table looking for an
;       entry that matches the specified function code passed in r1l.

cmd_btab_search:
                push    r2
                mov.w   #button_table,r2
cmd_btab_search_loop:
                mov.w   @r2,r0
                cmp.b   r1l,r0l
                beq     cmd_btab_search_found
                cmp.b   #h'ff,r0l
                beq     cmd_btab_search_fail
;       Not found, skip the rest of the record.
                mov.w   #12,r0
                add.w   r0,r2
                bra     cmd_btab_search_loop

;       End of table
;       Trick the caller into thinking that the returned value is
;       in the table. Remember, do not execute this entry!

cmd_btab_search_fail:
                mov.w   #bt_empty_entry,r0
                pop     r2
                rts

cmd_btab_search_found:
                mov.w   r2,r0
                pop     r2
                rts
;
;       Return the function code to match the button descriptor.
;       r1 == pointer to requested descriptor
;       return r0l with button function code.
;       tmp reg use:
;               r0 temp for compares, return value
;               r1 points to input buffer descriptor string
;               r2 points into the button table
;               r3 temp copy of r1
;               r4 temp for compares

cmd_btab_fc_search:
                push    r2
                push    r3
                push    r4

;       Downcase input descriptor

                mov.w   #4,r3
                mov.w   r1,r2
cmd_btab_fc_downcase:
                mov.b   @r2,r0l
                cmp.b   #  'A'  ,r0l
                blo     cmd_btab_fc_nodowncase
                cmp.b   #  'Z'  ,r0l
                bhi     cmd_btab_fc_nodowncase
                bset    #5,r0l
                mov.b   r0l,@r2
cmd_btab_fc_nodowncase:
                adds    #1,r2
                subs    #1,r3
                cmp.b   r3h,r3l
                bne     cmd_btab_fc_downcase

                mov.w   #button_table,r2
cmd_btab_fc_loop:
                mov.w   @r2,r0
                mov.b   r0l,@temporary
                mov.w   r1,r3
                adds    #2,r2
                adds    #2,r2
;       Compare first two bytes
                mov.b   @r3+,r0h
                mov.b   @r3+,r0l
                mov.w   @r2+,r4
                cmp.w   r0,r4
                bne     cmd_btab_fc_next
;       Compare second two bytes
                mov.b   @r3+,r0h
                mov.b   @r3+,r0l
                mov.w   @r2,r4

;       Do not incr r2, will do it later.

                cmp.w   r0,r4
                bne     cmd_btab_fc_next

;       Found it! Get the function code and return

                mov.b   @temporary,r0l
                bra     cmd_btab_fc_end

;       Look at next entry in table. If at end, return no code.

cmd_btab_fc_next:
                adds    #2,r2
                adds    #2,r2
                adds    #2,r2
                mov.w   @r2,r0
                mov.w   #h'ffff,r3
                cmp.w   r3,r0
                bne     cmd_btab_fc_loop
                mov.w   #FUNC_NOTHING,r0

cmd_btab_fc_end:
                pop     r4
                pop     r3
                pop     r2
                rts

; Execute a button function.

cmd_exec_button:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_exec_button_abort

;       This is not a real efficient way to search, but
;       I have the routines already written so I used
;       them. If this is a performance problem,
;       then we can fix up the search.

                mov.w   #button_table,r2
                jsr     cmd_btab_fc_search
                mov.b   r0l,r1l
                beq     cmd_exec_button_abort
                jsr     cmd_btab_search

;       r0 == button table entry

                adds    #2,r0
                mov.w   r0,r1
                mov.w   @r1,r0
                mov.w   #h'ffff,r1
                cmp.w   r1,r0
                beq     cmd_exec_button_exit
                jsr     @r0

cmd_exec_button_exit:
                rts
cmd_exec_button_abort:
                mov.w   #str_btab_illegal_spec,r1
                jmp     @@writeln_buffered_str
;
;----------------------------------------------------------
;
;       Print, or set the Calibration Value.
;
calv_error_1:
		pop	r0
calv_error:
                mov.w   #str_bad_number,r1
                jmp     @@write_buffered_str
cmd_calv:
                mov.w   #inp_buf,r1            
                jsr     cmd_skip_token         
                mov.b   @r1,r2l                
                beq     cmd_show_calv     
cmd_set_calv:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token



		jsr	read_dec_word                
					; Given the pointer to a string (r1) 
					; Convert to a binary value
					; Return decimal value (r0)
					; Ret zero set if ok
;
 		bne	calv_error
		cmp.b	#10,r0l		; is it in range 0-9
		bcc	calv_error
		push	r0
;
                jsr	read_dec_word
                cmp.b	#200,r0l
                bcc	calv_error_1
                mov.w	r0,@temp_rot_value
;
                mov.b   @current_config,r0l	; Given a configuration id (1-4) r0l
                jsr     get_config_ptr		; Ret address in R0
                				; enabled - cal val not set
                                                ; 4 ant  - 1 active high
                                                ; calibrate rot rate 0
		                                ; calibrate rot rate 1
                                                ; calibrate rot rate 2
                                                ; calibrate rot rate 3
                                                ; calibrate rot rate 4
                                                ; calibrate rot rate 5
                                                ; calibrate rot rate 6
                                                ; calibrate rot rate 7
                                                ; calibrate rot rate 8
                                                ; calibrate rot rate 9
                                                ; default rotation rate
		pop	r1
		push	r1
		add.w	r1,r0
		adds	#2,r0			; now points to rot to change
		mov.w	@temp_rot_value,r1
		mov.b	r1l,@r0
;
;       Show the antenna configuration
		mov.b   r1l,@calibration        ; correct calabration
		pop	r1
		jsr	set_rotation_rate	; to filters 
;
cmd_show_calv:
;
		jsr	write_current_config   
                jmp     util_write_calibrations


	

cmd_calv_set_fail:
                mov.w   #str_value_not_in_range,r1
                jsr     @@writeln_buffered_str
                mov.w   #str_calibration_not_set,r1
                jmp     @@writeln_buffered_str
;
;       Set these values in RAM to make them permanent do a SAVE
;       Also set cuttent calv in the
;       active rotation rate correction if required.

; ---------------------------------------------------------

;       Run the antenna check utility, same as startup.
;       In this case, set the "verbose" bit to print the
;       results to the console.

;       Print or set the voltage limits for the anntena check

;----------------------------------------------------------

cmd_acvoltage:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_acvoltage_show

                jsr     util_read_check_voltage
                bne     cmd_acvoltage_show
                mov.b   r0l,@antenna_voltage_too_low_d15

                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                bne     cmd_acvoltage_show

                jsr     util_read_check_voltage
                bne     cmd_acvoltage_show
                mov.b   r0l,@antenna_voltage_too_high_d244

                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                bne     cmd_acvoltage_show

                jsr     util_read_check_voltage
                bne     cmd_acvoltage_show
                mov.b   r0l,@antenna_voltage_same_delta_d14

cmd_acvoltage_show:
                mov.w   #str_acheck_min_limit,r1
                jsr     @@write_buffered_str
                mov.b   @antenna_voltage_too_low_d15,r0l
                jsr     util_write_check_voltage
                mov.w   #str_acheck_volts,r1
                jsr     @@write_buffered_str

                mov.w   #str_acheck_max_limit,r1
                jsr     @@write_buffered_str
                mov.b   @antenna_voltage_too_high_d244,r0l
                jsr     util_write_check_voltage
                mov.w   #str_acheck_volts,r1
                jsr     @@write_buffered_str

                mov.w   #str_acheck_delta_limit,r1
                jsr     @@write_buffered_str
                mov.b   @antenna_voltage_same_delta_d14,r0l
                jsr     util_write_check_voltage
                mov.w   #str_acheck_volts,r1
                jsr     @@write_buffered_str
                rts
;
; ---------------------------------------------------------
;
cmd_config:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_show_config

;       Determine if enabling or disabling an config
                mov.b   @r1,r4h
                cmp.b   #  '-'  ,r4h
                beq     cmd_config_do_en_dis
                cmp.b   #  '+'  ,r4h
                beq     cmd_config_do_en_dis

;       Set active set
                jsr     read_dec_word
                cmp.b   #0,r0l
                bls     cmd_config_error
                cmp.b   #4,r0l
                bhi     cmd_config_error

                jsr     util_set_active_configuration

                mov.b   @current_config,r0l
                jsr     get_config_ptr
                mov.b   #h'11,r1l       ; Make it active AND enabled.
                mov.b   r1l,@r0

                mov.b   #SEG_PAT_LOW_C,r1h
                mov.b   @current_config,r1l
                jsr     seg7_force_2display

                bra     cmd_show_config

cmd_config_do_en_dis:
                adds    #1,r1
                jsr     read_dec_word

                cmp.b   #0,r0l
                bls     cmd_config_error
                cmp.b   #4,r0l
                bhi     cmd_config_error

                jsr     get_config_ptr
                mov.b   @r0,r1l
                cmp.b   #  '-'  ,r4h
                bne     cmd_config_do_enable

;       Disable, as long as it is not active
                and     #h'f0,r1l
                beq     cmd_config_save_config_for_en_dis

                mov.w   #str_config_disable_error,r1
                jsr     @@writeln_buffered_str
                bra     cmd_show_config

cmd_config_do_enable:
                or      #h'01,r1l
cmd_config_save_config_for_en_dis:
                mov.b   r1l,@r0

                bra     cmd_show_config
;       End of enable disable section

cmd_config_error:
                mov.w   #str_config_error,r1
                jmp     @@writeln_buffered_str
;       jsr     @@writeln_buffered_str
;       rts

cmd_show_config:
                mov.b   #1,r2l
cmd_config_show_loop:
                mov.b   r2l,r0l
                jsr     get_config_ptr
                mov.w   r0,r3

                mov.b   @r3,r0l
;       Write the active char
                and     #h'f0,r0l
                beq     cmd_config_show_no_active
                mov.b   #  '*'  ,r1l
                bra     cmd_config_show_wr_act_char
cmd_config_show_no_active:
                mov.b   #  ' '  ,r1l
cmd_config_show_wr_act_char:
                jsr     @@write_buffered_char

;       Write out the config number
                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char
                mov.b   #  '#'  ,r1l
                jsr     @@write_buffered_char
                mov.b   r2l,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word

;       Antenna
                mov.w   #str_config_antenna,r1
                jsr     @@write_buffered_str

;       Check for disabled
                mov.b   @r3+,r0l
                and     #h'0f,r0l
                beq     cmd_show_disabled_config

;       Antenna config numbers
                mov.b   @r3,r0l
                and     #h'f0,r0l
                shlr    r0l
                shlr    r0l
                shlr    r0l
                shlr    r0l
                mov.w   #hex_table,r1
                add.w   r1,r0
                mov.b   @r0,r1l
                jsr     @@write_buffered_char

                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char

                mov.b   @r3+,r0l
                and     #h'0f,r0l
                beq     cmd_show_config_low
                mov.b   #  'H'  ,r1l
                bra     cmd_show_config_tenna_write
cmd_show_config_low:
                mov.b   #  'L'  ,r1l
cmd_show_config_tenna_write:
                jsr     @@write_buffered_char

;       Calibration string
                mov.w   #str_config_calibrations,r1
                jsr     @@write_buffered_str

;       Calibration values
                mov.b   #10,r4l
cmd_show_config_calv_loop:
                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char

                mov.b   @r3+,r0l
                jsr     write_padded_dec_byte
                subs    #1,r4
                cmp.b   #0,r4l
                bne     cmd_show_config_calv_loop

                bra     cmd_show_incr_loop

;       Write a disabled configuration

cmd_show_disabled_config:
                mov.w   #str_config_disabled,r1
                jsr     @@write_buffered_str
;       bra cmd_show_incr_loop

;       Done

cmd_show_incr_loop:
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
                adds    #1,r2
                cmp.b   #5,r2l
                beq     cmd_show_config_exit
                jmp     cmd_config_show_loop

cmd_show_config_exit:
                rts

cmd_help:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                beq     cmd_help_save_arg
                mov.b   #  'U'  ,r3l
                bra     cmd_help_start

cmd_help_save_arg:
                mov.b   @r1,r3l
                cmp.b   #  'a'  ,r3l
                blo     cmd_help_start
                and     #h'df,r3l       ; Clear lower case.

cmd_help_start:
                mov.w   #cli_cmd_table,r2

cmd_help_loop:
                mov.w   #h'ffff,r0
                mov.w   @r2,r1
                cmp.w   r0,r1
                beq     cmd_help_done
                adds    #2,r2           ; point to entry pt
                adds    #2,r2           ; point to help string
                mov.w   @r2+,r1
                beq     cmd_help_loop   ; If no help string, do not print it.

;       Restrict class of commands

                cmp.b   #  '!'  ,r3l
                beq     cmd_help_print
                mov.b   @r1,r3h
                cmp.b   r3l,r3h
                bne     cmd_help_loop
cmd_help_print:
                adds    #1,r1
                jsr     @@writeln_buffered_str
                bra     cmd_help_loop

cmd_help_done:
                rts

cmd_bearing:
                jsr     util_write_bearing
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_eeprom_write_test:

;       Write Byte value to eeprom
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_eeprom_write_test_fail

                mov.w   r1,r2
                jsr     read_word
                bne     cmd_eeprom_write_test_fail2
                mov.b   r0l,r4l
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                bne     cmd_eeprom_write_test_exit

                mov.w   r1,r2
                jsr     read_word
                bne     cmd_eeprom_write_test_exit

                mov.w   r0,r2
                mov.b   r4l,r1l
                jsr     eeprom_write_enable
                jsr     eeprom_write
                jsr     eeprom_write_disable

cmd_eeprom_write_test_exit:
                 rts

cmd_eeprom_write_test_fail:
                mov.w   #str_addr_not_in_range,r1
                jmp     @@writeln_buffered_str

cmd_eeprom_write_test_fail2:
                mov.w   #str_missing_arg,r1
                jmp     @@writeln_buffered_str

; eeprom read test
cmd_eeprom_read_test:

                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.w   r1,r2
                jsr     read_word
                bne     eeprom_read_fail

;       Read Value
                mov.b   r0l,r1l
                jsr     eeprom_read

;       Print value for confirmation
                mov.w   r0,r1
                jsr     @@write_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

eeprom_read_fail:
                mov.w   #str_addr_not_in_range,r1
                jmp     @@writeln_buffered_str
;
cmd_eedump:
;
;       eeprom print to memory. Displays the EEPROM.
;
                mov.b   #00,r4h			; address counter line
;
cmd_eedump_read_loop:
                mov.b   #00,r4l			; address counter per line
;
cmd_eedump_read_line_loop:
;
		mov.b	r4h,r1l
                jsr     eeprom_read		; get word (2 Bytes)
						; r1l address r0 data
;
		push	r0			; Print 2 Bytes
                mov.b   r0h,r1l			; with space after
                jsr     @@write_byte            ;     "
                mov.b	#' ',r1l                ;     "
		jsr     @@write_buffered_char   ;     "
		pop	r0                      ;     "
		mov.b	r0l,r1l                 ;     "
		jsr     @@write_byte            ;     "
                mov.b	#' ',r1l                ;     "
		jsr     @@write_buffered_char   ;     "
;
		inc	r4h			; next Word
		cmp.b	#(eeprom_ram_size/2),r4h ; last Word?
		beq	cmd_eedump_exit
                inc     r4l			; next position in line
                				; 2 bytes X 8 = 16 per line
                cmp.b   #8,r4l			; end of line?
                bne     cmd_eedump_read_line_loop

                mov.w   #eol_str,r1		; yes start new line
                jsr     @@write_buffered_str
		mov.b   #00,r4l
                bra     cmd_eedump_read_loop
cmd_eedump_exit:
		mov.w   #eol_str,r1		; new line
                jmp     @@write_buffered_str                
;
cmd_eeprom_zero:
;
;       Clear the EEPROM to all zeros.
;       When the doppler initializes, a zero EEPROM will be ignored.
;       This is also good for during software development when you
;       change the format of the saved persistant information.
;
                jsr     eeprom_write_enable

;       Write Byte value to eeprom

                mov.b   #h'00,r3l

cmd_eeprom_zero_loop:
                mov.b   r3l,r1l
                mov.w   #h'0000,r2
                jsr     eeprom_write
                inc     r3l
                mov.b   #h'80,r3h
                cmp.b   r3h,r3l
                bne     cmd_eeprom_zero_loop

                jmp     eeprom_write_disable
;
;----------------------------------------------------------
;
cmd_gps_set_speed:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                beq     cmd_speed_check_arg

cmd_min_speed_show:
                mov.b   @GPS_min_speed,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_speed_check_arg:
                jsr     read_dec_word		; r1 in r0 ret
                cmp.b   #20,r0l			; speed has to be below 20
                bhi     cmd_GPS_speed_bad
		mov.b	r0l,@GPS_min_speed
                rts

cmd_GPS_speed_bad:
                mov.w   #str_GPS_speed_high,r1
                jmp     @@writeln_buffered_str
;                
;----------------------------------------------------------
;
;       Show or set rotation rate.
;       With no argument, show rate.
;       With argument, set rate, with argument "-" show rate table.
;
cmd_rotation:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                beq     cmd_rotation_check_arg

cmd_rotation_show_config:
                mov.b   @current_rotation_rate,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_rotation_check_arg:
                mov.b   @r1,r0l
                cmp.b   #  '?'  ,r0l
                bne     cmd_rotation_set_config
                mov.w   #str_rotation_table,r1
                jmp     @@writeln_buffered_str

cmd_rotation_set_config:
                mov.w   r1,r2
                jsr     read_word
                mov.b   r0l,r1l
                cmp.b   #LAST_ROT,r1l
                bhi     cmd_rotation_bad
                jsr     set_rotation_rate
                mov.b   #SEG_PAT_LOW_R,r1h
                jsr     seg7_force_2display

cmd_rotation_done:
                rts

cmd_rotation_bad:
                mov.w   #str_rotation_out_range,r1
                jmp     @@writeln_buffered_str
;                
;----------------------------------------------------------
;
;       Stuff a value into the 7 segment display, for testing.
;       seg7 [##]
;
cmd_seg7:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_seg7_fail
                mov.w   r1,r2
                jsr     read_word
                bne     cmd_seg7_done
                and     #h'0f,r0l
                mov.b   r0l,r1l
                jmp     seg7_force_display

cmd_seg7_done:
                rts
cmd_seg7_fail:
                mov.w   #str_missing_arg,r1
                jmp     @@writeln_buffered_str

; Print the real time clock, and the test time diff algorithms.

cmd_time:
                mov.w   @rt_clock_hour,r2
                mov.w   #10,r0
                cmp.w   r0,r2
                bhi     cmd_time_no_pad_hour
                mov.b   #  '0'  ,r1l
                jsr     @@write_buffered_char
cmd_time_no_pad_hour:
                mov.w   r2,r1
                jsr     @@write_dec_word
                mov.b   #  ':'  ,r1l
                jsr     @@write_buffered_char

                mov.b   #0,r2h
                mov.b   @rt_clock_min,r2l
                cmp.b   #9,r2l
                bhi     cmd_time_no_min_pad
                mov.b   #  '0'  ,r1l
                jsr     @@write_buffered_char
cmd_time_no_min_pad:
                mov.w   r2,r1
                jsr     @@write_dec_word
                mov.b   #  ':'  ,r1l
                jsr     @@write_buffered_char

                mov.b   #0,r2h
                mov.b   @rt_clock_sec,r2l
                cmp.b   #9,r2l
                bhi     cmd_time_no_sec_pad
                mov.b   #  '0'  ,r1l
                jsr     @@write_buffered_char
cmd_time_no_sec_pad:
                mov.w   r2,r1
                jsr     @@write_dec_word

                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

;       Stop the doppler to stepper process.
;       Tell the pointer driver to move to the desired location.

cmd_stepto:
                mov.b   @ps_dial_out,r0l
                beq     cmd_stepto_doit
                mov.b   #0,r0l
                mov.b   r0l,@ps_dial_out
cmd_stepto_doit:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_stepto_fail
                jsr     read_dec_word
                mov.w   #h'c7,r1
                cmp.w   r0,r1
                bcc     cmd_stepto_in_range

;       Not in range 00 - c7 !

                mov.w   #str_value_not_in_range,r1
                jmp     @@writeln_buffered_str

cmd_stepto_in_range:
                mov.b   #2,r1l
                mulxu   r1l,r0
                mov.w   r0,@pointer_target

cmd_stepto_abort:
                rts
cmd_stepto_fail:
                mov.w   #str_missing_arg,r1
                jmp     @@writeln_buffered_str

cmd_ccw:
                mov.w   @pointer_target,r0
                mov.w   #1,r1
                sub.w   r1,r0
                bpl     cmd_ccw_doit
                mov.w   #h'18f,r0
cmd_ccw_doit:
                mov.w   r0,@pointer_target
;       Echo to the user
                mov.w   r0,r1
                mov.b   #2,r0l
                divxu   r0l,r1
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_cw:
                mov.w   @pointer_target,r0
                adds    #1,r0
                mov.w   #h'190,r1
                cmp.w   r1,r0
                bne     cmd_cw_doit
                mov.w   #0,r0
cmd_cw_doit:
                mov.w   r0,@pointer_target
;       Echo to the user
                mov.w   r0,r1
                mov.b   #2,r0l
                divxu   r0l,r1
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

; ---------------------------------------------------------

;       Add or remove options for the MicroFinder.
;               +t      use startup tones for error state
;               -t      do not use startup tones for error state
;               +k      make key click for buttons
;               -k      do not use key click
;               +p      pointer and dial work
;               -p      no pointer and stepper, turn off processes.
;               +g      Auto GPS stream echo + Bearing and Q 1 per Sec
;               -g      Byte Bearing  0 to 199   Byte Q  h'FQ on change
;               +0      Use old format of bearing for APRS compat
;               -0      Do not use old APRS format

;       Register use
;               r2l     ==0, remove ==1, add
;               r2h     option letter code

cmd_opt:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                beq     cmd_opt_do
                jmp     cmd_opt_show
;
cmd_opt_do:
                mov.b   @r1,r0l
                mov.b   #00,r2l			; Default False
                cmp.b   #  '+'  ,r0l
                bne     cmd_opt_false_flag

                mov.b   #01,r2l			; Make True
cmd_opt_false_flag:                
                adds    #1,r1			; Next Char
                mov.b   @r1,r0l
                bclr    #5,r0l			; Convert to upper case
;
cmd_opt_check_B:
		cmp.b   #  'B'  ,r0l		; Doppler bearing
                bne     cmd_opt_check_T
                cmp.b   #0,r2l
		bne     cmd_opt_add_bearing
cmd_opt_remove_bearing:
                mov.b   #0,r4L
                mov.b   r4L,@bearing_print_flag
                jmp     cmd_opt_exit
cmd_opt_add_bearing:
                mov.b   #1,r4L
                mov.b   r4L,@bearing_print_flag
                jmp     cmd_opt_exit

;;       OPTION Old APRS Compatibility
;
;cmd_opt_check3:
;                cmp.b   #  '0'  ,r0l
;                bne     cmd_opt_check4
;                cmp.b   #0,r2l
;                bne     cmd_opt_add_compatibility
;cmd_opt_remove_compatibility:
;                mov.b   #0,r4L
;                mov.b   r4L,@ctrl_byte_Old_APRS_compat
;                jmp     cmd_opt_exit
;cmd_opt_add_compatibility:
;                mov.b   #1,r4L
;                mov.b   r4L,@ctrl_byte_Old_APRS_compat
;                jmp     cmd_opt_exit
;
cmd_opt_check_T:
                cmp.b   #  'T'  ,r0l		; Startup tone option
                bne     cmd_opt_check_K
                cmp.b   #0,r2l
                bne     cmd_opt_add_tone
cmd_opt_remove_tone:

                mov.b   #0,r4L
                mov.b   r4L,@ctrl_byte_Start_tone
                jmp     cmd_opt_exit
cmd_opt_add_tone:

                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_Start_tone
                jmp     cmd_opt_exit
;                
cmd_opt_check_K:
                cmp.b   #  'K'  ,r0l		; Button click feedback
                bne     cmd_opt_check_P
                cmp.b   #0,r2l
                bne     cmd_opt_add_click
cmd_opt_remove_click:
                mov.b   #0,r4L
                mov.b   r4L,@ctrl_byte_Button_click
                bra     cmd_opt_exit
cmd_opt_add_click:
                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_Button_click
                bra     cmd_opt_exit
;
cmd_opt_check_P:
                cmp.b   #  'P'  ,r0l		; Pointer availability
                bne     cmd_opt_check_G
                cmp.b   #0,r2l
                bne     cmd_opt_add_pointer
cmd_opt_remove_pointer:
                mov.b   #0,r4L
                mov.b   r4L,@ctrl_byte_Pointer_avail
                mov.b   #PROCESS_STOPPED,r0l
                mov.b   r0l,@ps_dial_out
                mov.b   r0l,@ps_stepper_driver
                bra     cmd_opt_exit
cmd_opt_add_pointer:
                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_Pointer_avail
                mov.b   #PROCESS_RUNNING,r0l
                mov.b   r0l,@ps_dial_out
                mov.b   r0l,@ps_stepper_driver
                bra     cmd_opt_exit
;
cmd_opt_check_G:
                cmp.b   #  'G'  ,r0l		; GPS Streaming mode
                bne     cmd_opt_check_D
                cmp.b   #0,r2l
                bne     cmd_opt_add_gps
cmd_opt_remove_gps:
                mov.b   #0,r4L			; False
                mov.b   r4L,@GPS_echo_flag
                bra     cmd_opt_exit
cmd_opt_add_gps:
                mov.b   #1,r4L			; True
                mov.b   r4L,@GPS_echo_flag
                bra     cmd_opt_exit
;
cmd_opt_check_D:
                cmp.b   #  'D'  ,r0l		; Dim light mode
                bne     cmd_opt_check_A
                cmp.b   #0,r2l
                bne     cmd_opt_add_dim
cmd_opt_remove_dim:
                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_Dim_LED
                bra     cmd_opt_exit
cmd_opt_add_dim:
                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_Dim_LED
                bra     cmd_opt_exit

;       Turn off antenna checker

cmd_opt_check_A:
                cmp.b   #  'A'  ,r0l
                bne     cmd_opt_abort
                cmp.b   #0,r2l
                bne     cmd_opt_add_check
cmd_opt_remove_check:
                mov.b   #0,r4l
                mov.b   r4L,@ctrl_byte_CHECK_ANTENNA
                bra     cmd_opt_exit
cmd_opt_add_check:
                mov.b   #1,r4L
                mov.b   r4L,@ctrl_byte_CHECK_ANTENNA
                bra     cmd_opt_exit
;
cmd_opt_exit:
cmd_opt_abort:
cmd_opt_show:
;
                mov.b   @ctrl_byte_CHECK_ANTENNA,r4L	; Show Antenna Checker
                bne     cmd_show_no_check
cmd_show_check:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_check
cmd_show_no_check:
                mov.b   #  '-'  ,r1l
cmd_show_write_check:
                jsr     @@write_buffered_char
                mov.w   #str_antenna_checker,r1
                jsr     @@writeln_buffered_str
;
                mov.b   @ctrl_byte_Dim_LED,r4L		; Show DIM LED MODE
                beq     cmd_show_no_dim_led
cmd_show_dim_led:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_dim
cmd_show_no_dim_led:
                mov.b   #  '-'  ,r1l
cmd_show_write_dim:
                jsr     @@write_buffered_char
                mov.w   #str_dim_led,r1
                jsr     @@writeln_buffered_str
;
                mov.b   @GPS_echo_flag,r4L		; Show GPS Streaming
                beq     cmd_show_Byte_bearing_Q
cmd_show_gps:
                mov.w   #str_GPSs,r1
                jsr     @@writeln_buffered_str
                bra     cmd_show_bearing_flag
cmd_show_Byte_bearing_Q:
                mov.w   #str_B_Q,r1
                jsr     @@writeln_buffered_str
;                
cmd_show_bearing_flag:
                mov.b   @Bearing_print_flag,r4L
                beq     cmd_show_no_bearing
cmd_show_bearing:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_bearing
cmd_show_no_bearing:
                mov.b   #  '-'  ,r1l
cmd_show_write_bearing:
                jsr     @@write_buffered_char
                mov.w   #str_bearing_print,r1
                jsr     @@writeln_buffered_str
;                
                mov.b   @ctrl_byte_Start_tone,r3H	; Show startup tone
                beq     cmd_show_no_tone
cmd_show_tone:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_tone
cmd_show_no_tone:
                mov.b   #  '-'  ,r1l
cmd_show_write_tone:
                jsr     @@write_buffered_char
                mov.w   #str_start_tone,r1
                jsr     @@writeln_buffered_str

;       Show Button Click

                mov.b   @ctrl_byte_Button_click,r3H
                beq     cmd_show_no_click
cmd_show_click:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_click
cmd_show_no_click:
                mov.b   #  '-'  ,r1l
cmd_show_write_click:
                jsr     @@write_buffered_char
                mov.w   #str_button_click,r1
                jsr     @@writeln_buffered_str

;       Show pointer avail

                mov.b   @ctrl_byte_Pointer_avail,r4L
                beq     cmd_show_no_pointer
cmd_show_pointer:
                mov.b   #  '+'  ,r1l
                bra     cmd_show_write_pointer
cmd_show_no_pointer:
                mov.b   #  '-'  ,r1l
cmd_show_write_pointer:
                jsr     @@write_buffered_char
                mov.w   #str_pointer,r1
                jsr     @@writeln_buffered_str
;
;       Show old APRS Compat

                mov.b   @ctrl_byte_Old_APRS_compat,r3H
                beq     cmd_show_exit
cmd_show_compa:
                mov.b   #  '+'  ,r1l
                jsr     @@write_buffered_char
                mov.w   #str_compat,r1
                jsr     @@writeln_buffered_str

cmd_show_exit:
                rts

;       Light leds in the ring using the value 0..200.
;       Mainly for testing
;       This command turns off the LED ring display

cmd_ledto:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_ledto_fail
                mov.w   r1,r2           ; Used for read_dec_word

                jsr     read_dec_word
                mov.b   r0l,r1l         ; Set named LED
                mov.b   #0,r1h          ; No blink bit
                jsr     util_set_dop_deg_to_led

                mov.b   #PROCESS_STOPPED,r0l
                mov.b   r0l,@ps_led_ring_display

cmd_ledto_exit:
                rts
cmd_ledto_fail:
                mov.w   #str_missing_arg,r1
                jmp     @@writeln_buffered_str
;
cmd_multd:
		mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                beq     cmd_multd_check_arg

cmd_multd_show:
                mov.b   @LED8_out_RED,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.b   @LED8_out_GREEN,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.b   @LED8_iner_RED,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.b   @LED8_iner_GREEN,r1l
                mov.b   #0,r1h
                jsr     @@write_dec_word
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_multd_check_arg:
                jsr     read_dec_word		; r1 in r0 ret
                cmp.b   #max_filter/2 - 1,r0l 
                bhi     cmd_multd_bad
		mov.b	r0l,@LED8_out_RED
		jsr     read_dec_word		; r1 in r0 ret
                cmp.b   #max_filter/2 - 1,r0l 
                bhi     cmd_multd_bad
		mov.b	r0l,@LED8_out_GREEN
		jsr     read_dec_word		; r1 in r0 ret
                cmp.b   #max_filter/2 - 1,r0l 
                bhi     cmd_multd_bad
		mov.b	r0l,@LED8_iner_RED
		jsr     read_dec_word		; r1 in r0 ret
                cmp.b   #max_filter/2 - 1,r0l 
                bhi     cmd_multd_bad
		mov.b	r0l,@LED8_iner_GREEN
                rts

cmd_multd_bad:
                mov.w   #str_multd_high,r1
                jmp     @@writeln_buffered_str
cmd_multd_exit:
                rts

;
;       Set the owner`s call.

cmd_mycall:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_mycall_exit

                mov.w   #str_prompt,r0
                mov.b   #8,r3h
                mov.b   #1,r3l
cmd_mycall_copy_loop:
                mov.b   @r1+,r2l
                cmp.b   #  ' '  ,r2l
                blo     cmd_mycall_terminate
                mov.b   r2l,@r0
                adds    #1,r0
                sub.b   r3l,r3h
                bne     cmd_mycall_copy_loop

cmd_mycall_terminate:
                mov.b   #  ' '  ,r1l
                mov.b   r1l,@r0
                adds    #1,r0
                mov.b   #0,r1l
                mov.b   r1l,@r0

cmd_mycall_exit:
                rts

;       Print the process status. Show all processes
;       and their run/stop/sleep status.
;       Register usage:
;               r1 - Temp / Calc
;               r2 - Process table ptr.
;               r3 - Temp / Calc
;               r4h - Boolean - verbose printout.
;               r4l - Holds stop/sleep/run state.

cmd_ps:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_get_boolean_token
                mov.b   r0l,r4h

                mov.w   #proc_header,r1
                jsr     @@writeln_buffered_str

                mov.w   #process_table,r2

cmd_ps_loop:
                mov.w   @r2+,r3
                mov.w   #h'ffff,r1
                cmp.w   r1,r3
                bne     cmd_ps_continue
                rts

cmd_ps_continue:
                mov.b   @r3,r4l ; Load process state
                adds    #2,r2

                mov.w   r2,r1   ; Get process name
                jsr     write_buffered_4char

                cmp.b   #PROCESS_STOPPED,r4l
                bne     cmd_ps_other
                mov.w   #proc_stopped,r1
                bra     cmd_ps_write_state
cmd_ps_other:
                cmp.b   #PROCESS_SLEEP,r4l
                bne     cmd_ps_is_running
                mov.w   #proc_sleep,r1
                bra     cmd_ps_write_state
cmd_ps_is_running:
                mov.w   #proc_run,r1
cmd_ps_write_state:
                jsr     @@write_buffered_str

cmd_ps_skip_drivers:
                adds    #2,r2
                adds    #2,r2
                adds    #2,r2
;       Print or skip over descriptive string.
                cmp.b   #0,r4h
                beq     cmd_ps_end_of_line
                mov.w   @r2,r1
                jsr     @@write_buffered_str

cmd_ps_end_of_line:
                mov.w   #eol_str,r1
                jsr     @@write_buffered_str
                adds    #2,r2
                bra     cmd_ps_loop
;
cmd_read_byte:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token

;       Utility, given buffer in r1,
;       skip it along till we hit a space
;       then skip white space.
;       Return pointer in r1.

                mov.w   r1,r2
                jsr     read_word

;       Make a 16 bit value from 4 or (fewer) characters
;       pointed to by r2
;       Return the result in r0
;       r3 used as an accumulator

                bne     cmd_read_byte_error
cmd_read_byte_ok:
                mov.b   @r0,r1l
                push    r0
                jsr     @@write_byte
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char

                pop     r0
                adds    #1,r0
                mov.b   r0L,R1L
                and     #h'0f,r1L
                bne     cmd_read_byte_ok
                mov.w   #eol_str,r1
                jmp     @@write_buffered_str
;
cmd_read_byte_error:
                mov.w   #str_addr_not_in_range,r1
                jmp     @@writeln_buffered_str

cmd_read_word:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                mov.w   r1,r2

                jsr     read_word
                bne     cmd_read_word_error

;       Not going to read anything other than RAM
;                mov.w   #serial_number,r2
;                cmp.w   r2,r0
;                beq     cmd_read_word_ok
;                mov.w   #READ_BYTE_LOWER_LIMIT,r2
;                cmp.w   r2,r0
;                bls     cmd_read_word_error

cmd_read_word_ok:
                mov.b   @r0+,r1h
                mov.b   @r0+,r1l
                push    r0
                jsr     @@write_word
                mov.b   # ' ' ,r1L
                jsr     @@write_buffered_char
                pop     r0
                mov.b   r0L,r1L
                and     #h'0f,r1L
                bne     cmd_read_word_ok

                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

cmd_read_word_error:
                mov.w   #str_addr_not_in_range,r1
                jmp     @@writeln_buffered_str

cmd_stop:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_find_process
                mov.w   #0,r2
                cmp.w   r2,r0
                beq     cmd_stop_not_found

                mov.b   #0,r1l
                mov.w   @r0,r2
                mov.b   r1l,@r2
                rts

cmd_stop_not_found:
                mov.w   #str_process_not_found,r1
                jmp     @@writeln_buffered_str

cmd_gpsout:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                bne     cmd_snoop_exit
                jsr     cmd_get_boolean_token
                cmp.b   #0,r0l
                bne     cmd_snoop_on

cmd_snoop_off:
                mov.b   #PROCESS_STOPPED,r0l
                mov.b   r0l,@ps_aprs_snooper
                bra     cmd_snoop_other_args

cmd_snoop_on:
                mov.b   #PROCESS_SLEEP,r0l
                mov.b   r0l,@ps_aprs_snooper
                mov.w   @snooper_constant,r0
                mov.w   r0,@rt_sec_snooper
;       bra     cmd_snoop_other_args

cmd_snoop_other_args:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                bne     cmd_snoop_exit
                jsr     read_dec_word
                bcc     cmd_snoop_input_err
                cmp.b   #9,r0l
                bhi     cmd_snoop_input_err
                mov.b   r0l,@snooper_qlevel

                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                bne     cmd_snoop_exit
                jsr     read_dec_word
                bcc     cmd_snoop_input_err

;       Limit range to 50 minutes

                mov.w   #0,r1
                cmp.w   r1,r0
                beq     cmd_snoop_input_err
                mov.w   #3000,r1
                cmp.w   r1,r0
                bhi     cmd_snoop_input_err

                mov.w   r0,@snooper_constant
                mov.w   r0,@rt_sec_snooper
                bra     cmd_snoop_exit

cmd_snoop_input_err:
                mov.w   #str_value_not_in_range,r1
                jsr     @@writeln_buffered_str

cmd_snoop_exit:
                mov.w   #str_gpsout,r1
                jsr     @@write_buffered_str
                mov.b   @ps_aprs_snooper,r0l
                bne     cmd_snoop_show_on
cmd_snoop_show_off:
                mov.w   #str_off,r1
                bra     cmd_snoop_show_rest
cmd_snoop_show_on:
                mov.w   #str_on,r1
cmd_snoop_show_rest:
                jsr     @@write_buffered_str
                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char

                mov.b   @snooper_qlevel,r1l
		mov.b	#0,r1h
                jsr     @@write_dec_word

                mov.b   #  ' '  ,r1l
                jsr     @@write_buffered_char
                mov.w   @snooper_constant,r1
                jsr     @@write_dec_word

                mov.w   #eol_str,r1
                jmp     @@write_buffered_str

;----------------------------------------------------------

;       Run the process specified by argument 1

cmd_run:
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_find_process
                mov.w   #0,r2
                cmp.w   r2,r0
                beq             cmd_run_not_found

                mov.b   #PROCESS_RUNNING,r1l
                mov.w   @r0,r2
                mov.b   r1l,@r2
                rts

cmd_run_not_found:
                mov.w   #str_process_not_found,r1
                jmp     @@writeln_buffered_str

;       Write the byte in memory as requested by the user.
;       Register usage:

;       r1 - Temp for inp buffer ptr calcs.
;       r2 - Parameter passing to read_word
;       r3 - Temp, holds binary address.

cmd_write_byte:
                mov.w   #inp_buf,r1
;       Skip the command token
                jsr     cmd_skip_token
                mov.w   r1,r2
;       Convert the address
                jsr     read_word
                bne     cmd_write_byte_error
                mov.w   r0,r3
;       Convert the byte value.
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                mov.w   r1,r2
                jsr     read_word
                bne     cmd_write_byte_exit
;       Now do the write
                mov.b   r0l,@r3
                rts

cmd_write_byte_error:
                mov.w   #str_addr_not_in_range,r1
                jsr     @@writeln_buffered_str
cmd_write_byte_exit:
                rts

;       Write the word in memory as requested by the user.
;       Register usage:
;       r1 - Temp for inp buffer ptr calcs.
;       r2 - Parameter passing to read_word
;       r3 - Temp, holds binary address.

cmd_write_word:
                mov.w   #inp_buf,r1
;       Skip the command token
                jsr     cmd_skip_token
                mov.w   r1,r2
;       Convert the address
                jsr     read_word
                bne     cmd_write_word_error
                mov.w   r0,r3
;       Convert the byte value.
                mov.w   #inp_buf,r1
                jsr     cmd_skip_token
                jsr     cmd_skip_token
                mov.w   r1,r2
                jsr     read_word
                bne     cmd_write_word_error
;       Now do the write
                mov.b   r0h,@r3
                adds    #1,r3
                mov.b   r0l,@r3
                rts

cmd_write_word_error:
                mov.w   #str_addr_not_in_range,r1
                jsr     @@writeln_buffered_str
cmd_write_word_exit:
                rts

;       Utility, given buffer in r1, convert the char to boolean.
;
;       	1 | T | H == true  (1)
; anything but  1 | T | H == false (0)
;       value returned in r0l

cmd_get_boolean_token:
                mov.b   @r1,r0l

                cmp.b   #'1',r0l
                beq     cmd_get_boolean_true

                and     #h'df,r0l       ; Clear lower case.
                cmp.b   #  'T'  ,r0l
                beq     cmd_get_boolean_true

                cmp.b   #  'H'  ,r0l
                beq     cmd_get_boolean_true

cmd_get_boolean_false:			; If it's not true
                mov.b   #0,r0l
                rts

cmd_get_boolean_true:
                mov.b   #1,r0l
                rts
;
;----------------------------------------------------------
;
;       Utility, given buffer in r1, skip it along till
;       we hit a space then skip white space.
;       Return pointer in r1.
;	Return char in r0l.
;	If end of line found then ret with zero flag clear
;
cmd_skip_token:
                mov.b   @r1,r0l
                beq     cmd_skip_token_done

                cmp.b   #  ' '  ,r0l
                bls     cmd_skip_token_space
                adds    #1,r1
                bra     cmd_skip_token

cmd_skip_token_space:
                cmp.b   #  ' '  ,r0l
                bhi     cmd_skip_token_done
                cmp.b   #0,r0l
                beq     cmd_skip_token_done
                adds    #1,r1
                mov.b   @r1,r0l
                bra     cmd_skip_token_space

cmd_skip_token_done:
                mov.b   @r1,r0l
                xorc    #4,ccr          ; change Zero flag
                rts
;
;----------------------------------------------------------
;
;       String pointed to by r1 has a descriptor for the process.
;       Search the process tables till we find a match.

;       Register usage:
;               r0 - Pointer to the found process descriptor, or NIL
;               r1 - Points to requested descriptor buffer
;               r2 - Temp for user`s pid
;               r3 - Temp for candidate process`s pid
;               r4 - Temp for comparisons

cmd_find_process:
                push    r2
                push    r3
                push    r4

;       Downcase input descriptor

                mov.w   #4,r3
                mov.w   r1,r2
cmd_find_process_downcase:
                mov.b   @r2,r0l
                cmp.b   #  'A'  ,r0l
                blo     cmd_find_process_nodowncase
                cmp.b   #  'Z'  ,r0l
                bhi     cmd_find_process_nodowncase
                bset    #5,r0l
                mov.b   r0l,@r2
cmd_find_process_nodowncase:
                adds    #1,r2
                subs    #1,r3
                cmp.b   r3h,r3l
                bne     cmd_find_process_downcase

                mov.w   #process_table,r0
cmd_find_process_loop:
                mov.w   @r0,r2
                mov.w   #h'ffff,r3
                cmp.w   r2,r3
                beq     cmd_find_process_not_found

                mov.w   r1,r2
;       Make r3 point to process`s pid
                mov.w   r0,r3
                adds    #2,r3
                adds    #2,r3

;       Now compare (char 1)
                mov.b   @r2+,r4h
                mov.b   @r3+,r4l
                cmp.b   r4h,r4l
                bne     cmd_find_process_next
;       (char 2)
                mov.b   @r2+,r4h
                mov.b   @r3+,r4l
                cmp.b   r4h,r4l
                bne     cmd_find_process_next
;       (char 3)
                mov.b   @r2+,r4h
                mov.b   @r3+,r4l
                cmp.b   r4h,r4l
                bne     cmd_find_process_next
;       (char 4)
                mov.b   @r2+,r4h
                mov.b   @r3+,r4l
                cmp.b   r4h,r4l
                bne     cmd_find_process_next

;       If we made it here, we found it...

                bra     cmd_find_process_exit

cmd_find_process_next:
                mov.w   #12,r4
                add.w   r4,r0
                bra     cmd_find_process_loop

cmd_find_process_not_found:
                mov.w   #0,r0

cmd_find_process_exit:
                pop     r4
                pop     r3
                pop     r2
                rts

fence_cmd_end:
;
; ---------------------------------------------------------
;
fence_table_start:
;
rotation_table:
;
;      freq = 3.93 MHz / 200 filter clock / 2(Rate + 1)
;
                                ;       About
                .data.b 60      ; 0     202
                .data.b 50      ; 1     241
                .data.b 40      ; 2     300
                .data.b 32      ; 3     373
                .data.b 26      ; 4     455
                .data.b 22      ; 5     534
                .data.b 18      ; 6     647
                .data.b 15      ; 7     768
                .data.b 12      ; 8     946
                .data.b 10      ; 9    1118
;

;       Antenna switching state machines.

;       The antenna table looks like:
;		output port 2 drives antennas
;		P20 = Ant 1 ... P27 = Ant 8
;               byte antenna_pattern = switch high.
;			selected Ant high & unused high
;		byte antenna_pattern = switch low
;			Selected Ant low 
;               byte antenna number
;		byte next switch time
;               word( next_state )

;       Note: Antenna number is used by the ISR when scheduling filtering operations.

;       Trick: Unused antenna leads are kept high, this way we can
;       use them as cheapie power leads.

;       Four

antenna_4_isr:
                .data.b  h'F1		; 1111 0001 active high
                .data.b  h'FE		; 1111 1110 active low
                .data.b  1
                .data.b  25
                .data.w antenna_4_isr_2
antenna_4_isr_2:
                .data.b  h'F2		; 1111 0010
                .data.b  h'FD		; 1111 1101
                .data.b  2
                .data.b  75
                .data.w antenna_4_isr_3
antenna_4_isr_3:
                .data.b  h'F4		; 1111 0100
                .data.b  h'FB		; 1111 1011
                .data.b  3
                .data.b  125
                .data.w antenna_4_isr_4
antenna_4_isr_4:
                .data.b  h'F8		; 1111 1000
                .data.b  h'F7		; 1111 0111
                .data.b  4
                .data.b  175
                .data.w antenna_4_isr
                
;       Six

antenna_6_isr:
                .data.b  h'c1
                .data.b  h'fE
                .data.b  1
                .data.b  43
                .data.w antenna_6_isr_2
antenna_6_isr_2:
                .data.b  h'c2
                .data.b  h'fD
                .data.b  2
                .data.b  76
                .data.w antenna_6_isr_3
antenna_6_isr_3:
                .data.b  h'c4
                .data.b  h'fB
                .data.b  3
                .data.b  110
                .data.w antenna_6_isr_4
antenna_6_isr_4:
                .data.b  h'c8
                .data.b  h'f7
                .data.b  4
                .data.b  142
                .data.w antenna_6_isr_5
antenna_6_isr_5:
                .data.b  h'd0
                .data.b  h'ef
                .data.b  5
                .data.b  176
                .data.w antenna_6_isr_6
antenna_6_isr_6:
                .data.b  h'e0
                .data.b  h'df
                .data.b  6
                .data.b  10
                .data.w antenna_6_isr

;       Eight

antenna_8_isr:
                .data.b  h'01
                .data.b  h'fE
                .data.b  1
                .data.b  35
                .data.w antenna_8_isr_2
antenna_8_isr_2:
                .data.b  h'02
                .data.b  h'fD
                .data.b  2
                .data.b  60
                .data.w antenna_8_isr_3
antenna_8_isr_3:
                .data.b  h'04
                .data.b  h'fb
                .data.b  3
                .data.b  85
                .data.w antenna_8_isr_4
antenna_8_isr_4:
                .data.b  h'08
                .data.b  h'f7
                .data.b  4
                .data.b  110
                .data.w antenna_8_isr_5
antenna_8_isr_5:
                .data.b  h'10
                .data.b  h'ef
                .data.b  5
                .data.b  135
                .data.w antenna_8_isr_6
antenna_8_isr_6:
                .data.b  h'20
                .data.b  h'df
                .data.b  6
                .data.b  160
                .data.w antenna_8_isr_7
antenna_8_isr_7:
                .data.b  h'40
                .data.b  h'bf
                .data.b  7
                .data.b  185
                .data.w antenna_8_isr_8
antenna_8_isr_8:
                .data.b  h'80
                .data.b  h'7f
                .data.b  8
                .data.b  10
                .data.w antenna_8_isr

; ---------------------------------------------------------

stepper_table:
;       Each data record is composed of three words:
;               data word
;               forward link
;               backward link
;       Links are used to reduce the amount of address
;       calculation needed.

;       Each data word (16 bits) has 2 hex bytes.
;       These are used as:
;               byte1 byte2
;               byte1 - Motor pattern Rev 1 hardware
;               byte2 - Motor pattern Rev 0 hardware
;                       <bit 7 = motor signal>
;                       <bit 5 = motor signal>
;                       <bit 4 = motor signal>
;                       <bit 3 = light on>
;                       <bit 2 = high for pull up on radiator bit>
;                       <bit 1 = motor signal>
;                       <bit 0 = keep on stepping>

;       Explanation of bit 0 is in the stepper driver.
;
;       Each byte is designed to be sent directly to the motor port (P9).
;       Hardware layout is the reason that the motor bits are not adjacent.
;
;       The main difference between the two hardware rev motor signals
;       is swaping some of the motor signals around so the motors can be
;       directly installed with the plug from the floppy drive, and will
;       require not cut & try to make the motor work.
;
;	st_1 thru st_8 = 400 steps per rev
;
;					motor bits
;				  1 34   2   1 34   2   1423  1423
st_1:                                                   7415  7415
                .data.w h'8C8C	; 1000 1100  1000 1100  1000  1000
                .data.w st_2
                .data.w st_8
;
st_2:           .data.w h'DDCF	; 1101 1101  1100 1111  1100  1010
                .data.w st_3
                .data.w st_1
;
st_3:           .data.w h'5C4E	; 0101 1100  0100 1110  0100  0010
                .data.w st_4
                .data.w st_2
;
st_4:           .data.w h'5E6E	; 0101 1110  1110 1110  0110  0011 error? 5f6e
                .data.w st_5
                .data.w st_3
;
st_5:           .data.w h'0E2C	; 0000 1110  0010 1100  0010  0001
                .data.w st_6
                .data.w st_4
;
st_6:           .data.w h'2F3D	; 0010 1111  0011 1101  0011  0101
                .data.w st_7
                .data.w st_5
;
st_7:           .data.w h'2C1C	; 0010 1100  0001 1100  0001  0100
                .data.w st_8
                .data.w st_6
;
st_8:           .data.w h'AD9D	; 1010 1101  1001 1101  1001  1100
                .data.w st_1	;  N   BZ N
                .data.w st_7	;  C   L  C
;	So why do bits 6 and 0 change?
;
; ---------------------------------------------------------
;
;	4 LED Display table a total of 8 leds in each display.
;
;	289.8, 315.0, 336.6, 354.6, 5.4, 23.4,45.0, 70.2 Degrees
;	161,   175,   187,   197,   3,   13,  25,   39   Doppler degrees
;	  0      1      2      3    4     5    6     7   hex address of leds
;
;	To allow 2 leds on at the "same time"
;       and to keep the same intensity hex F = off.
;	Each byte in the table has a High and Low nibble
;	to display 0 degrees both 3 and 4 must be on.
;	the driver will alternate between High and Low nibble.
;	To keep the same intensity 5.4 degrees will switch between 4 and F.
;	as a special case 270 and 90 degrees will tuen on 0 or 7 at full intensity.
;	After 90 and before 270 both 0 and 7 will be on to indicate it's behind you.
;	This range will be calculated to shorten the table.
;
; Data for LED8 displays
;		RED uper nibble	GREEN lower nibble
;		Positive going clock (P81) for outer LEDS
;		Negitive for the iner LEDS
;		Information from table needs to be converted 
;		from high and low nibble to be inserted into
;		odd-even byte for the correct display
;
;	LED8_out_odd:			.res.b	1
;	LED8_out_even:			.res.b	1
;	LED8_iner_odd:			.res.b	1
;	LED8_iner_even:			.res.b	1
;
; Used by command to assign witch filter to which display
;	.data.b  0		; LED8_out_RED
;	.data.b  1		; LED8_out_GREEN
;	.data.b  2		; LED8_iner_red
;	.data.b  3		; LED8_iner_GREEN
;
; Example:
;	DD from filter 0 = 194 result from table = 23 hex
;	DD from filter 1 = 7   result from table = 45 hex
; Start by placing the 23 in LED8_out_odd:
; and the 45 in LED8_out_even: 
; Bit manipulation required to put the 3 of 23 in the 
; uper nibble of LED8_out_odd:
; and the 4 of 45 in the lower nibble of LED8_out_even:
;
; Result:
; 	LED8_out_odd:  = 24 
;	LED8_out_even: = 35
;
; This needs to be done after all the filters have new values
;
;
; ---------------------------------------------------------
;
LED8_table:
			; doppler degrees
	
	.data.b  h'34	; 000
	.data.b  h'34	; 001
	.data.b  h'4f	; 002
	.data.b  h'4f	; 003
	.data.b  h'4f	; 004
	.data.b  h'45	; 005
	.data.b  h'45	; 006
	.data.b  h'45	; 007
	.data.b  h'45	; 008
	.data.b  h'45	; 009
	.data.b  h'5f	; 010
	.data.b  h'5f	; 011
	.data.b  h'5f	; 012
	.data.b  h'5f	; 013
	.data.b  h'5f	; 014
	.data.b  h'5f	; 015
	.data.b  h'5f	; 016
	.data.b  h'56	; 017
	.data.b  h'56	; 018
	.data.b  h'56	; 019
	.data.b  h'56	; 020
	.data.b  h'56	; 021
	.data.b  h'56	; 022
	.data.b  h'6f	; 023
	.data.b  h'6f	; 024
	.data.b  h'66	; 025
	.data.b  h'6f	; 026
	.data.b  h'6f	; 027
	.data.b  h'6f	; 028
	.data.b  h'6f	; 029
	.data.b  h'67	; 030
	.data.b  h'67	; 031
	.data.b  h'67	; 032
	.data.b  h'67	; 033
	.data.b  h'67	; 034
	.data.b  h'67	; 035
	.data.b  h'7f	; 036
	.data.b  h'7f	; 037
	.data.b  h'7f	; 038
	.data.b  h'7f	; 039
	.data.b  h'7f	; 040
	.data.b  h'7f	; 041
	.data.b  h'7f	; 042
	.data.b  h'7f	; 043
	.data.b  h'7f	; 044
	.data.b  h'7f	; 045
	.data.b  h'7f	; 046
	.data.b  h'7f	; 047
	.data.b  h'7f	; 048
	.data.b  h'77	; 049
	.data.b  h'77	; 050
	.data.b  h'77	; 051
;		 h'07	; 052 - 147
;
	.data.b  h'00	; 148	77	51
	.data.b  h'00	; 149	77	50
	.data.b  h'00	; 150	77	49
	.data.b  h'0f	; 151	7f	48
	.data.b  h'0f	; 152	7f	47
	.data.b  h'0f	; 153	7f	46
	.data.b  h'0f	; 154	7f	45
	.data.b  h'0f	; 155	7f	44
	.data.b  h'0f	; 156	7f	43
	.data.b  h'0f	; 157	7f	42
	.data.b  h'0f	; 158	7f	41
	.data.b  h'0f	; 159	7f	40
	.data.b  h'0f	; 160	7f	39
	.data.b  h'0f	; 161	7f	38
	.data.b  h'0f	; 162	7f	37
	.data.b  h'0f	; 163	7f	36
	.data.b  h'01	; 164	67	35
	.data.b  h'01	; 165	67	34
	.data.b  h'01	; 166	67	33
	.data.b  h'01	; 167	67	32
	.data.b  h'01	; 168	67	31
	.data.b  h'01	; 169	67	30
	.data.b  h'1f	; 170	6f	29
	.data.b  h'1f	; 171	6f	28
	.data.b  h'1f	; 172	6f	27
	.data.b  h'1f	; 173	6f	26
	.data.b  h'11	; 174	66	25
	.data.b  h'1f	; 175	6f	24
	.data.b  h'1f	; 176	6f	23
	.data.b  h'12	; 177	56	22
	.data.b  h'12	; 178	56	21
	.data.b  h'12	; 179	55	20
	.data.b  h'12	; 180	56	19
	.data.b  h'12	; 181	56	18
	.data.b  h'12	; 182	56	17
	.data.b  h'2f	; 183	5f	16
	.data.b  h'2f	; 184	5f	15
	.data.b  h'2f	; 185	5f	14
	.data.b  h'2f	; 186	5f	13
	.data.b  h'2f	; 187	5f	12
	.data.b  h'2f	; 188	5f	11
	.data.b  h'2f	; 189	5f	10
	.data.b  h'23	; 190	45	09
	.data.b  h'23	; 191	45	08
	.data.b  h'23	; 192	45	07
	.data.b  h'23	; 193	45	06
	.data.b  h'23	; 194	45	05
	.data.b  h'3f	; 195	4f	04
	.data.b  h'3f	; 196	4f	03
	.data.b  h'3f	; 197	4f	02
	.data.b  h'34	; 198	34	01
	.data.b  h'34	; 199	34	00
;	
; ---------------------------------------------------------
;
;       This is the process table

process_table:

pt_buttin:      .data.w         ps_buttin
                .data.w         p_buttin
                .sdata  "butt"
                .data.w         0
                .data.w         pstr_buttin

pt_lcd:      	.data.w         ps_lcd
                .data.w         p_lcd
                .sdata  "blcd"
                .data.w         rt_msec_lcd
                .data.w         pstr_lcd                

pt_attractor:   .data.w         ps_attractor
                .data.w         p_attractor
                .sdata  "attr"
                .data.w         0
                .data.w         pstr_attractor

pt_led_ring_display:
		.data.w    	ps_led_ring_display
                .data.w         p_led_ring_display
                .sdata  "ledR"
                .data.w         rt_msec_led_ring_process
                .data.w         pstr_led_ring_display

pt_dial_out:    .data.w         ps_dial_out
                .data.w         p_dial_out
                .sdata  "dout"
                .data.w         0
                .data.w         pstr_dial_out

pt_analog:      .data.w         ps_analog
                .data.w         p_analog
                .sdata  "alog"
                .data.w         0
                .data.w         pstr_analog

pt_serial_in:   .data.w         ps_serial_in
                .data.w         p_serial_in
                .sdata  "s in"
                .data.w         0
                .data.w         pstr_serial_in

pt_stepper:     .data.w         ps_stepper_driver
                .data.w         p_stepper_driver
                .sdata  "step"
                .data.w         rt_msec_stepper
                .data.w         pstr_stepper_driver

pt_led_driver:  .data.w         ps_led_driver
                .data.w         p_led_driver
                .sdata  "ledD"
                .data.w         0
                .data.w         pstr_led_driver

pt_calibrate:   .data.w         ps_calibrate
                .data.w         p_calibrate
                .sdata  "cala"
                .data.w         0
                .data.w         pstr_calibrate

pt_sound_driver:
                .data.w         ps_sound_driver
                .data.w         p_sound_driver
                .sdata  "sond"
                .data.w         rt_msec_sounder
                .data.w         pstr_sound_driver


;       Always keep this here, this indicates the end of the table.
pt_end_of_table:
                .data.w         h'ffff

; -------------------------------------------------------------------------

;       Button Function Table

;       function code   (word - low order byte)
;       entry pt                (address)
;       fid             (char[4])
;       0               (16 bit word)
;       description string      (address)

button_table:

bt_attract:     .data.w FUNC_ATTRACT            ; 2
                .data.w         button_attract  ; 2 entry pt
                .sdata  "batt"                  ; 4
                .data.w         0               ; 2
                .data.w         bstr_attract    ; 2
                                        ; Total 12

bt_bearing:     .data.w         FUNC_BEARING    ; Send to computer
                .data.w         button_bearing
                .sdata  "brng"
                .data.w         0
                .data.w         bstr_bearing

;bt_bearing_n_gps:
;                .data.w         FUNC_BEARING_N_GPS      ; send to computer
;                .data.w         button_bearing_n_gps
;                .sdata  "bbng"
;                .data.w         0
;                .data.w         bstr_bearing_n_gps

bt_calibrate:   .data.w         FUNC_CALIBRATE
                .data.w         button_calibrate
                .sdata  "bcal"
                .data.w         0
                .data.w         bstr_calibrate
bt_check_antenna:
                .data.w         FUNC_CHECK_ANTENNA
                .data.w         button_check_antenna
                .sdata  "bchk"
                .data.w         0
                .data.w  bstr_check_antenna

bt_config:      .data.w         FUNC_CONFIG		; 0f
                .data.w         button_config
                .sdata  "bcfg"
                .data.w         0
                .data.w         bstr_config
;
;       function code   (word - low order byte)
;       entry pt                (address)
;       fid             (char[4])
;       0               (16 bit word)
;       description string      (address)
;
bt_pointer_on_off:
                .data.w         FUNC_PTR_ON_OFF
                .data.w         button_ptr_on_off
                .sdata  "bpoo"
                .data.w         0
                .data.w         bstr_ptr_on_off
;
bt_rot:
                .data.w         FUNC_ROT        ; Change rotation frequency
                .data.w         button_rot
                .sdata  "brot"
                .data.w         0
                .data.w         bstr_rot
;                
bt_threshold:
		.data.w         FUNC_THRESHOLD 	; change Q Threshold 
                .data.w         button_threshold
                .sdata  "bthd"
                .data.w         0
                .data.w         bstr_threshold
;                
bt_sample_size:
		.data.w         FUNC_SAMPLE_SIZE ; change filter sample size 
                .data.w         button_sample_size
                .sdata  "bsss"
                .data.w         0
                .data.w         bstr_sample_size                                
;
bt_hold:                .data.w FUNC_HOLD       ; Stop LED display
                .data.w         button_hold
                .sdata  "bhld"
                .data.w 0
                .data.w         bstr_hold
;                
;       function code   (word - low order byte)
;       entry pt                (address)
;       fid             (char[4])
;       0               (16 bit word)
;       description string      (address)                
;
; LED -----------------------------------------------------------------

bt_ledf:        .data.w FUNC_LED_FILT   	; What filter to use with LEDs
                .data.w         button_ledf
                .sdata  "blfl"
                .data.w 0
                .data.w         bstr_ledf
                
bt_leda:                .data.w FUNC_LED_ABS    ; Absoulte-Relative bearing LEDs
                .data.w         button_leda
                .sdata  "blfa"
                .data.w 0
                .data.w         bstr_leda

bt_led_speed:   .data.w         FUNC_LED_SPEED
                .data.w         button_led_speed
                .sdata  "blpt"
                .data.w         0
                .data.w         bstr_led_speed
                
bt_dim:         .data.w         FUNC_DIM_LED
                .data.w button_dim
                .sdata  "bdim"
                .data.w         0
                .data.w         bstr_dim
;
; Pointer -------------------------------------------------------------                
;
bt_ptrf:                .data.w FUNC_PTR_FILT   ; What filter to use with PTR
                .data.w         button_ptrf
                .sdata  "bpfl"
                .data.w 0
                .data.w         bstr_ptrf
                
bt_ptra:                .data.w FUNC_PTR_ABS    ; Absoulte-Relative bearing PTR
                .data.w         button_ptra
                .sdata  "bpfa"
                .data.w 0
                .data.w         bstr_ptra

bt_ptrspeed:    .data.w         FUNC_PTR_SPEED    ; Pointer speed
                .data.w         button_pointer
                .sdata  "bptr"
                .data.w         0
                .data.w         bstr_ptrsp
;
; ---------------------------------------------------------------------
;
bt_lcda:	.data.w         FUNC_LCD_A	; LCD absolute bearing filter
                .data.w         button_lcda
                .sdata  "blca"
                .data.w         0
                .data.w         bstr_lcd_ab
                
bt_lcdr:	.data.w         FUNC_LCD_R	; LCD reliative bearing filter
                .data.w         button_lcdr
                .sdata  "blcr"
                .data.w         0
                .data.w         bstr_lcd_rel                
;
;       function code   (word - low order byte)
;       entry pt                (address)
;       fid             (char[4])
;       0               (16 bit word)
;       description string      (address)
;
bt_save:                .data.w FUNC_SAVE       ; Save EEPROM values
                .data.w         button_save
                .sdata  "bsav"
                .data.w         0
                .data.w         bstr_save

bt_cust_1:      .data.w         FUNC_CUST_1
                .data.w         button_cust_1
                .sdata  "bcf1"
                .data.w         0
                .data.w         bstr_custom_1

bt_cust_2:      .data.w         FUNC_CUST_2
                .data.w         button_cust_2
                .sdata  "bcf2"
                .data.w         0
                .data.w         bstr_custom_2

bt_cust_3:      .data.w         FUNC_CUST_3
                .data.w         button_cust_3
                .sdata  "bcf3"
                .data.w         0
                .data.w         bstr_custom_3

bt_cust_4:      .data.w         FUNC_CUST_4
                .data.w         button_cust_4
                .sdata  "bcf4"
                .data.w         0
                .data.w         bstr_custom_4

;       Do not remove this word, it is the end of all button table.
bt_end:         .data.w h'ffff

;       CLI command table

cli_cmd_table:
;		.data.w cmd_str_GPRMC			; Parse GPS
;               .data.w cmd_GPS				; get Speed
;               .data.w 0				; get bearing 
                
;       Set the check voltages for the antenna check
                .data.w cmd_str_acvoltage
                .data.w cmd_acvoltage
                .data.w cmd_help_acvoltage

                .data.w cmd_str_alarm
                .data.w cmd_alarm
                .data.w cmd_help_alarm

                .data.w cmd_str_asw
                .data.w cmd_asw
                .data.w cmd_help_asw

                .data.w cmd_str_baud
                .data.w cmd_baud
                .data.w cmd_help_baud

                .data.w cmd_str_bearing
                .data.w cmd_bearing
                .data.w cmd_help_bearing

                .data.w cmd_str_btab
                .data.w cmd_btab
                .data.w cmd_help_btab

                .data.w cmd_str_calv
                .data.w cmd_calv
                .data.w cmd_help_calv

                .data.w cmd_str_ccw
                .data.w cmd_ccw
                .data.w cmd_help_ccw

                .data.w cmd_str_cw
                .data.w cmd_cw
                .data.w cmd_help_cw

                .data.w cmd_str_check_antenna
                .data.w cmd_check_antenna
                .data.w cmd_help_check_antenna

                .data.w cmd_str_config
                .data.w cmd_config
                .data.w cmd_help_config

                .data.w cmd_str_eedump
                .data.w cmd_eedump
                .data.w cmd_help_eedump

                .data.w cmd_str_eeprom
                .data.w cmd_eeprom_write_test
                .data.w cmd_help_eeprom

                .data.w cmd_str_eezero
                .data.w cmd_eeprom_zero
                .data.w cmd_help_eezero

                .data.w cmd_str_exec_button
                .data.w cmd_exec_button
                .data.w cmd_help_exec_button
                
                .data.w cmd_str_gpsout
                .data.w cmd_gpsout
                .data.w cmd_help_gpsout

                .data.w cmd_str_gps_min_speed		; gpss
                .data.w cmd_gps_set_speed
                .data.w cmd_help_gps_min_speed
;       help
                .data.w cmd_str_help
                .data.w cmd_help
                .data.w cmd_help_help
;       ?
                .data.w cmd_str_help_qm
                .data.w cmd_help
                .data.w 0
;       Do not print help for this one
;
;       ledto
                .data.w cmd_str_ledto
                .data.w cmd_ledto
                .data.w cmd_help_ledto
;       multd
                .data.w cmd_str_multd
                .data.w cmd_multd
                .data.w cmd_help_multd                
                

;       mycall
                .data.w cmd_str_mycall
                .data.w cmd_mycall
                .data.w 0
;       Do not print help for this one

                .data.w cmd_str_opt
                .data.w cmd_opt
                .data.w cmd_help_opt

                .data.w cmd_str_ps
                .data.w cmd_ps
                .data.w cmd_help_ps

                .data.w cmd_str_readb
                .data.w cmd_read_byte
                .data.w cmd_help_readb

                .data.w cmd_str_readw
                .data.w cmd_read_word
                .data.w cmd_help_readw

                .data.w cmd_str_reset
                .data.w main
                .data.w cmd_help_reset

                .data.w cmd_str_rotation
                .data.w cmd_rotation
                .data.w cmd_help_rotation

                .data.w cmd_str_run
                .data.w cmd_run
                .data.w cmd_help_run

                .data.w cmd_str_eesave
                .data.w cmd_eeprom_save
                .data.w cmd_help_eesave

                .data.w cmd_str_seg7
                .data.w cmd_seg7
                .data.w cmd_help_seg7

                .data.w cmd_str_stepto
                .data.w cmd_stepto
                .data.w cmd_help_stepto

                .data.w cmd_str_stop
                .data.w cmd_stop
                .data.w cmd_help_stop

                .data.w cmd_str_time
                .data.w cmd_time
                .data.w cmd_help_time

                .data.w cmd_str_writeb
                .data.w cmd_write_byte
                .data.w cmd_help_writeb

                .data.w cmd_str_writew
                .data.w cmd_write_word
                .data.w cmd_help_writew

                .data.w h'ffff  ; This MUST be here

;       NEVER over write this or
;       the cli processor will fall of the end!

; This is a list of string for button #, during "btab" command.

str_button_list:
                .data.w str_button_1
                .data.w str_button_2
                .data.w str_button_3
                .data.w str_button_4
                .data.w str_button_5
                .data.w str_button_6
                .data.w str_button_7
                .data.w str_button_8
                .data.w str_button_9
                .data.w str_button_10
                .data.w str_button_11
                .data.w str_button_12
                .data.w str_button_13
                .data.w str_button_14
                .data.w str_button_15
                .data.w str_button_16

;       This is a fake entry used for empty button functions.
;       We should never execute an entry that says "Nothing".

bt_empty_entry: .data.w         FUNC_NOTHING
                .data.w         h'ffff
                .sdata          "...."
                .data.w         0
                .data.w         str_button_unknown

;       Hook routines for patches.
;       Load start address in these locations.
;       Typically done after manufacture of EPROM.
;       Routine is placed in empty memory and one of
;       the hook routines is blown.

start_hook_1:
                .data.w h'ffff
start_hook_2:
                .data.w h'ffff
start_hook_3:
                .data.w h'ffff
start_hook_4:
                .data.w h'ffff

;       Table of patterns to be used for
;       the seven segment display

led_7seg_patterns:
                .data.w seg7_pattern_0
                .data.w seg7_pattern_1
                .data.w seg7_pattern_2
                .data.w seg7_pattern_3
                .data.w seg7_pattern_4
                .data.w seg7_pattern_5
                .data.w seg7_pattern_6
                .data.w seg7_pattern_7
                .data.w seg7_pattern_8
                .data.w seg7_pattern_9
                .data.w seg7_pattern_A
                .data.w seg7_pattern_B
                .data.w seg7_pattern_C
                .data.w seg7_pattern_D
                .data.w seg7_pattern_E
                .data.w seg7_pattern_F
                .data.w seg7_pattern_G
                .data.w seg7_pattern_dash
                .data.w seg7_pattern_bar1
                .data.w seg7_pattern_bar2
                .data.w seg7_pattern_bar3
                .data.w seg7_pattern_dot
                .data.w seg7_pattern_k1
                .data.w seg7_pattern_k2
                .data.w seg7_pattern_k3
                .data.w seg7_pattern_k4
                .data.w seg7_pattern_low_c
                .data.w seg7_pattern_low_n
                .data.w seg7_pattern_h
                .data.w seg7_pattern_s
                .data.w seg7_pattern_w
                .data.w seg7_pattern_c_dot
                .data.w seg7_pattern_f_dot
                .data.w seg7_pattern_p
                .data.w seg7_pattern_low_r
                .data.w seg7_pattern_l
                .data.w seg7_pattern_low_0_dot
                .data.w seg7_pattern_5_dot

fence_table_end:

; ---------------------------------------------------------

fence_string_start:

welcome_str:
 .sdata "\n\r"
 .sdata  "*********************************\n\r"
 .sdata  "*      MicroFinder Doppler      *\n\r"
 .sdata  "*    (C) Copyright 1996-2014    *\n\r"
 .sdata  "*      All rights reserved.     *\n\r"
 .sdata  "*                               *\n\r"
 .sdata  "*       AHHA! Solutions         *\n\r"
 .sdata  "*   KE6GDD KE6GDH KN6FW KN6ZT   *\n\r"
 .sdata  "*                               *\n\r"
 .sdata  "*  Version FW1.3    2014-01-28  *\n\r"
 .sdataz "*********************************\n\r"
;
str_lcd_line1:
		
		.data.b	h'8c,h'b8,h'80
		.sdata  "C 555 An 444 Lrn"
;			 1234567890123456
		.data.b	h'c0
		.sdata  "R5 Q9 Rn 666 Prn"
		.data.b	h'ff
str_lcd_line1_end:
lcd_length: 	.equ	str_lcd_line1_end - str_lcd_line1
;
str_error_ant_1:
                .sdataz "Antenna 1 overrun.\n\r"
bad_hex:        .sdataz "Bad Hex number.\n\r"
str_bad_number: .sdataz "Bad input\n\r"

eol_str:        .data.b  CR
line_feed:      .data.b  LF
                .data.b  0

;       Option descriptors
str_antenna_checker:
                .sdataz "a / Antenna check"
str_dim_led:
                .sdataz "d / Dim LED"
str_GPSs:
                .sdataz "+g / GPS + Bearing Q"
str_B_Q:
                .sdataz "-g / Byte Bearing and Q"
str_bearing_print:
                .sdataz "b / Bearing print"
str_start_tone:
                .sdataz "t / Startup tone"
str_compat:
                .sdataz "0 / Old APRS compat"
str_pointer:
                .sdataz "p / Pointer"
str_button_click:
                .sdataz "k / Button click"

;       MicroFinder can parse these

str_gprmc_parse:
                .sdataz "$gprmc"
;
str_bslash:
                .sdataz "\\"
str_eh:
                .sdataz "????"
str_baud_error:
                .sdataz "Rate error"

proc_header:
                .sdataz "PROC  STATE"
proc_sleep:
                .sdataz     "  sleep "
proc_stopped:
                .sdataz     "  stop  "
proc_run:
                .sdataz     "  run   "

;       Strings for printing the configuration table

str_config_antenna:
                .sdataz " Antenna "
str_config_calibrations:
                .sdataz " Calibrations"
str_config_disabled:
                .sdataz "- - Calibrations --- --- --- --- ---"
str_config_error:
                .sdataz "Bad configuration number"
str_config_disable_error:
                .sdataz "Can not disable the active configuration"

;       Strings for antenna checking

str_acheck_header:
                .sdataz "Antenna / Volts"
str_acheck_spacer:
                .sdataz  " "
str_acheck_sep:
                .sdataz " / "
str_acheck_min_limit:
                .sdataz "Minimum "
str_acheck_max_limit:
                .sdataz "Maximum "
str_acheck_delta_limit:
                .sdataz "Element Delta "
str_acheck_volts:
                .sdataz " Volts\n\r"
str_ant_chk_broken:
                .sdata  "\n\r*******************\n\r"
                .sdataz     " VOLTAGE ANTENNA CONDITION"
str_ant_chk_broken2:
                .sdataz "\n\r*******************\n\r"
str_ant_chk_space:
                .sdataz "\n\r     "
str_ant_chk_space2:
                .sdataz             "     "

str_ant_chk_Open_E:
                .sdata  "Open ERROR"
                .data.b 7,0
str_ant_chk_Ok:
                .sdataz "Ok"
str_ant_chk_Low:
                .sdata  "Low or Shorted"
                .data.b 7,0
str_ant_chk_active:
                .sdataz "Active"

str_ant_chk_D_know:
                .sdataz "Don't Know"
str_ant_chk_Extra:
                .sdata  "Too many Antennas"
                .data.b 7,0
str_ant_chk_Not_same:
                .sdata  "Diode drops don't match"
                .data.b 7,0

str_unknown_command:
                .data.b 7                       ; bell
                .sdataz "What?"
str_unimplemented:
                .sdataz "Unimplemented\n\r"
str_calibration_header:
                .sdataz "Calibration = "
str_quality:
                .sdataz "Quality threshold = "
str_qfilt:
                        .sdataz "Queue filter (qual limit/miss limit/min depth) = "
str_rotation_table:
                        .sdataz "ROT Rate 0 thru 9 "
str_rotation_out_range:
                        .sdataz "Invalid rate."
str_GPS_speed_high:
                        .sdataz "GPS speed too high. max 19"
str_current_config:
			.sdataz "Current Config "
str_antenna_is:
                        .sdataz "\r\nAntenna elements : "
str_antenna_sw_hi:
                        .sdataz " H"
                        ;"Antenna switch  : high" ; changed 2011-12-30
str_antenna_sw_lo:
			.sdataz " L"
;                        .sdataz "Antenna switch   : low"	; changed 2011-12-30
str_antenna_bad_count:
                        .sdataz "Illegal number of antenna elements."
str_button_unknown:
                        .sdataz "............................"
str_btab_illegal_spec:
                        .sdataz "Bad function specification"
str_btab_illegal_button_no:
                        .sdataz "Bad button number"
str_btab_in_calibrate_mode:
                        .sdataz "Btns #1, #2, #3, & #4 in calibrate mode."
str_button_1:
                        .sdataz "Btn #1 : "
str_button_2:
                        .sdataz "Btn #2 : "
str_button_3:
                        .sdataz "Btn #3 : "
str_button_4:
                        .sdataz "Btn #4 : "
str_button_5:
                        .sdataz "Btn #5 : "
str_button_6:
                        .sdataz "Btn #6 : "
str_button_7:
                        .sdataz "Btn #7 : "
str_button_8:
                        .sdataz "Btn #8 : "
str_button_9:
                        .sdataz "Btn #9 : "
str_button_10:
                        .sdataz "Btn #10 : "
str_button_11:
                        .sdataz "Btn #11 : "
str_button_12:
                        .sdataz "Btn #12 : "
str_button_13:
                        .sdataz "Btn #13 : "
str_button_14:
                        .sdataz "Btn #14 : "
str_button_15:
                        .sdataz "Btn #15 : "
str_button_16:
                        .sdataz "Btn #16 : "
str_serin_overflow:
                        .sdataz "*** Input Buffer Overflow\n\r"
str_cancel:
                        .sdataz "\n\r*** Canceled\n\r"
str_eedump_separator:
                        .sdataz " - "
str_eedump_space:
                        .sdataz " "
str_eeprom_version_mismatch:
                        .sdataz "Unknown EEPROM version.\n\r"
str_eeprom_not_loaded:
                        .sdataz "\n\r\n\rEEPROM load aborted, defaults installed."
str_process_not_found:
                        .sdataz "Process id bad."
str_addr_not_in_range:
                        .sdataz "Address is not in range"
str_missing_arg:
                        .sdataz "Missing value for command"
str_multd_high:
			.sdataz "Value exceeds maximum"                       
str_compass_error:
                        .sdataz "Compass error"
str_value_not_in_range:
                        .sdataz "Value is not in range."
str_calibration_not_set:
                        .sdataz "Calibration not set."
str_point_no_zero:
                        .sdataz "Pointer not zeroed correctly."
str_calibrating_rate:
                        .sdataz "Calibrating "
str_gpsout:
                        .sdataz "GPS out   (on=1/off=0, qlevel 0-9, delay 0 not allowed)> "
str_on:
                        .sdataz "on"
str_off:
                        .sdataz "off"
str_seconds:
                        .sdataz " seconds"
str_knots:
                        .sdataz " knots"
str_gps_GPRMC:
                        .sdataz "GPRMC"
;GPRMC_x:
;GPRMC_size:              .equ   GPRMC_x - str_gps_GPRMC

str_soft_brk:
                        .sdataz "\n\rSoftware Break at "
str_reg_display:
                        .sdataz "\n\r R0   R1   R2   R3   R4   R5   R6   SP  IUHUNZVC"
uart0_str:              .sdataz "Command serial "
uart1_str:              .sdataz "Second serial  "
;
hex_table:              .data.b                 h'30
                        .data.b                 h'31
                        .data.b                 h'32
                        .data.b                 h'33
                        .data.b                 h'34
                        .data.b                 h'35
                        .data.b                 h'36
                        .data.b                 h'37
                        .data.b                 h'38
                        .data.b                 h'39
                        .data.b                 h'41
                        .data.b                 h'42
                        .data.b                 h'43
                        .data.b                 h'44
                        .data.b                 h'45
                        .data.b                 h'46
;
;       7 Segment display tables
;       referenced in the index table

;       [f] --a-- [b]
;       [f]       [b]
;       [f]       [b]
;           --g--
;       [e]       [c]
;       [e]       [c]
;       [e] --d-- [c] [h]

seg7_pattern_0:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_E
                        .data.b  SEG7_F
                        .data.b  0

seg7_pattern_1:         .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_2:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_3:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_G
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_4:         .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_5:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_6:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  SEG7_C
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_7:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_8:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_E
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_9:         .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_A:         .data.b  SEG7_E
                        .data.b  SEG7_F
                        .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_B:         .data.b  SEG7_F
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  SEG7_C
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_C:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_D:         .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_E
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_E:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_F:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  0

seg7_pattern_G:         .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_dash:      .data.b  SEG7_G
                        .data.b  0

seg7_pattern_bar1:      .data.b  SEG7_D
                        .data.b  0

seg7_pattern_bar2:      .data.b  SEG7_D
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_bar3:      .data.b  SEG7_D
                        .data.b  SEG7_G
                        .data.b  SEG7_A
                        .data.b  0

seg7_pattern_dot:       .data.b  SEG7_DOT
                        .data.b  0

seg7_pattern_k1:        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  0

seg7_pattern_k2:        .data.b  SEG7_B
                        .data.b  SEG7_G
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_k3:        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  SEG7_C
                        .data.b  SEG7_G
                        .data.b  SEG7_A
                        .data.b  0

seg7_pattern_k4:        .data.b  SEG7_F
                        .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_G
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_low_c:     .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_low_n:     .data.b  SEG7_E
                        .data.b  SEG7_G
                        .data.b  SEG7_C
                        .data.b  0

seg7_pattern_h:         .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_E
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_s:         .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  0

seg7_pattern_w:         .data.b  SEG7_B
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_E
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  0

seg7_pattern_c_dot:     .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_E
                        .data.b  SEG7_D
                        .data.b  SEG7_DOT
                        .data.b  0

seg7_pattern_f_dot:     .data.b  SEG7_A
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  SEG7_DOT
                        .data.b  0

seg7_pattern_p:         .data.b  SEG7_A
                        .data.b  SEG7_B
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_E
                        .data.b  0

seg7_pattern_low_r:     .data.b  SEG7_G		;       [f] --a-- [b]
                        .data.b  SEG7_E         ;       [f]       [b]
                        .data.b  0              ;       [f]       [b]
                                                ;           --g--    
seg7_pattern_l:         .data.b  SEG7_F		;       [e]       [c]
                        .data.b  SEG7_E         ;       [e]       [c]
                        .data.b  SEG7_D         ;       [e] --d-- [c] [h]
                        .data.b  0              
seg7_pattern_low_0_dot:
			.data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_E
                        .data.b  SEG7_G
                        .data.b  SEG7_DOT
                        .data.b  0
seg7_pattern_5_dot:
			.data.b  SEG7_A
                        .data.b  SEG7_C
                        .data.b  SEG7_D
                        .data.b  SEG7_F
                        .data.b  SEG7_G
                        .data.b  SEG7_DOT
                        .data.b  0
;
; GPS "comand"
;cmd_help_GPS:
;cmd_str_GPRMC:
;			.sdataz "$gprmc"

; User commands
cmd_str_asw:
                        .sdataz "as*w"
cmd_help_asw:
                        .sdataz "Uasw       [# L|H]      Show or set the antenna configuration"
cmd_str_baud:
                        .sdataz "ba*ud"
cmd_help_baud:
                        .sdataz "Ubaud      [12|24|48|96] Set or show serial baud rate"
cmd_str_bearing:
                        .sdataz "be*aring"
cmd_help_bearing:
                        .sdataz "Ubearing                Display current bearing in rel,abs degrees"
cmd_str_btab:
                        .sdataz "bt*ab"
cmd_help_btab:
                        .sdataz "Ubtab      [B# F#] | ?  Show or set the button functions"
cmd_str_check_antenna:
                        .sdataz "ch*kantenna"
cmd_help_check_antenna:
                        .sdataz "Uchkantenna             Check antenna switch"
cmd_str_compass:
                        .sdataz "com*pass"
cmd_help_compass:
                        .sdataz "Ucompass                Display the current compass value"
cmd_str_eesave:
                        .sdataz "save"
cmd_help_eesave:
                        .sdataz "Usave                   Save current configuration"
cmd_str_gps_min_speed:
                        .sdataz "gpss"
cmd_help_gps_min_speed:
                        .sdataz "Ugpss      ##           set min GPS speed"                        
cmd_str_help:
                        .sdataz "h*elp"
cmd_str_help_qm:
                        .sdataz "?"
cmd_help_help:
                        .sdataz "Uhelp      [u|a|d|!]    Help for User, Advanced, Debug, or All!"
cmd_str_ledto:
                        .sdataz "l*edto"
cmd_help_ledto:
                        .sdataz "Dledto     #            Light LED 0..200"
cmd_help_multd:
                        .sdataz "Umultd     # # # #      Show or set filter to LED8 display"
cmd_str_multd:
                        .sdataz "mu*ltd"                        
cmd_str_mycall:
                        .sdataz "my*call"
cmd_str_reset:
                        .sdataz "reset"
cmd_help_reset:
                        .sdataz "Ureset                  Reset to power on configuration"

;       Advanced commands

cmd_str_acvoltage:
                        .sdataz "acv*oltage"
cmd_help_acvoltage:
                        .sdataz "Aacvoltage [low_v hi_v delta_v] Show or set the voltage levels for chkantenna"

cmd_str_alarm:
                        .sdataz "al*arm"
cmd_help_alarm:
                        .sdataz "Aalarm     [#sec]       Sound alarm if filtered bearing lost for #sec"
cmd_str_calv:
                        .sdataz "ca*lv"
cmd_help_calv:
                        .sdataz "Acalv      [# ##] | -   Show or set the calibration value for a rate"
cmd_str_config:
                        .sdataz "con*fig"
cmd_help_config:
                        .sdataz "Aconfig    [-][#]       Set active config (w/ arg) or show all"
cmd_str_exec_button:
                        .sdataz "ex*ecbtn"
cmd_help_exec_button:
                        .sdataz "Aexecbtn   XXXX         Execute button function XXXX"
cmd_str_gpsout:
                        .sdataz "gpso*ut"
cmd_help_gpsout:
                        .sdataz "Agpsout    t|f [q [d]]  on|off, quality, delay"                        
cmd_str_gpsmv:
                        .sdataz "gpsm*invel"
cmd_help_gpsmv:
                        .sdataz "Agpsminvel #            Minimum acceptable velocity to use GPS heading"
cmd_str_gps_retain:
                        .sdataz "gpsr*etain"
cmd_help_gps_retain:
                        .sdataz "Agpsretain #            Amount of seconds to retain last good GPS sentence"
cmd_str_gps:
                        .sdataz "gpsc*apture"
cmd_str_opt:
                        .sdataz "o*pt"
cmd_help_opt:
                        .sdataz "Aopt       [+/-X]       Add or remove option (see manual)"
cmd_str_ps:
                        .sdataz "ps"
cmd_help_ps:
                        .sdataz "Aps        [t|f]        List process states, use arg for full list"
cmd_str_qual:
                        .sdataz "qu*al"
cmd_help_qual:
                        .sdataz "Aqual                   Display current quality measurement"
cmd_str_qual_threshold:
                        .sdataz "qt*hresh"
cmd_help_qual_threshold:
                        .sdataz "Aqthresh   ####         Set # of good samples for reflection reject"
cmd_str_rotation:
                        .sdataz "ro*tation"
cmd_help_rotation:
                        .sdataz "Arotation  [0-9]        Set or show rotation rate"
cmd_str_run:
                        .sdataz "run"
cmd_help_run:
                        .sdataz "Arun       XXXX         Cause process XXXX to start running"
cmd_str_stop:
                        .sdataz "stop"
cmd_help_stop:
                        .sdataz "Astop      XXXX         Cause process XXXX to stop running"
cmd_str_qfilt:
                        .sdataz "qf*ilt"
cmd_help_qfilt:
                        .sdataz "Aqfilt     [QQ MISS DEPTH] Set or show queue filter params"

;       Debug commands

cmd_str_ccw:
                        .sdataz  "cc*w"
cmd_help_ccw:
                        .sdataz "Dccw                    Move pointer 1 step ccw"
cmd_str_cw:
                        .sdataz "cw"
cmd_help_cw:
                        .sdataz "Dcw                     Move pointer 1 step cw"
cmd_str_eedump:
                        .sdataz "eed*ump"
cmd_help_eedump:
                        .sdataz "Deedump                 Print out the EEPROM to screen"
cmd_str_eeprom:
                        .sdataz "eew*rite"
cmd_help_eeprom:
                        .sdataz "Deewrite   ## ####      Write a value to EEPROM"
cmd_str_eezero:
                        .sdataz "eez*ero"
cmd_help_eezero:
                        .sdataz "Deezero                 Clear EEPROM"
cmd_str_readb:
                        .sdataz "rb*yte"
cmd_help_readb:
                        .sdataz "Drbyte     AAAA         Read a byte from memory"
cmd_str_readw:
                        .sdataz "rw*ord"
cmd_help_readw:
                        .sdataz "Drword     AAAA         Read a word from memory"
cmd_str_seg7:
                        .sdataz "se*g7"
cmd_help_seg7:
                        .sdataz "Dseg7      [#]          Stuff hex digit into the 7 segment display"
cmd_str_stepto:
                        .sdataz "st*epto"
cmd_help_stepto:
                        .sdataz "Dstepto    ####         Move pointer to location [000-199]"
cmd_str_time:
                        .sdataz "t*ime"
cmd_help_time:
                        .sdataz "Dtime                   Print real time clock value"
cmd_str_writeb:
                        .sdataz "wb*yte"
cmd_help_writeb:
                        .sdataz "Dwbyte     AAAA ##      Write a byte to memory"
cmd_str_writew:
                        .sdataz "ww*ord"
cmd_help_writew:
                        .sdataz "Dwword     AAAA ####    Write a word to memory"

;       Process description strings

pstr_serial_in:
                        .sdataz "RS-232 input"
pstr_serial_output:
                        .sdataz "RS-232 output"
pstr_buttin:
                        .sdataz "Button input"
pstr_lcd:
			.sdataz "lcd display"
pstr_attractor:
                        .sdataz "IMPRESS your friends"
pstr_led_ring_display:
                        .sdataz "Display doppler or compass"
pstr_snooper:
                        .sdataz "Send doppler data out serial line"
pstr_analog:
                        .sdataz "Analog inputs."
pstr_dial_out:
                        .sdataz "Doppler pointer"
pstr_stepper_driver:
                        .sdataz "Stepper motor driver"
pstr_led_driver:
                        .sdataz "Manage LED display"
pstr_calibrate:
                        .sdataz "Calibration driver"
pstr_compass_calibrate:
                        .sdataz "Compass calibration driver"
pstr_sound_driver:
                        .sdataz "Sounder driver"
pstr_alarm:
                        .sdataz "Lost signal alarm"

;       Button Function Desription Strings

bstr_separator:
                        .sdataz "   "
bstr_rot_rate_cal:
			.sdataz "\n\rR0   R1   R2   R3   R4   R5   R6   R7   R8   R9\n\r"
bstr_antennas:
			.sdataz " Antennas Active "
                                                
; Print strings -------------------------------------------------------
bstr_bearing:
                        .sdataz "Print current bearing"
bstr_bearing_n_gps:
                        .sdataz "Print bearing and captured gps string"
bstr_gps:
                        .sdataz "Print last valid captured GPS sentence"
                        
; Pointer strings -----------------------------------------------------
bstr_ptrf:
                        .sdataz "Pointer filter"
bstr_ptra:
                        .sdataz "Pointer absolute-relative"
bstr_ptrsp:
                        .sdataz "Pointer speed"
bstr_ptr_on_off:
                        .sdataz "Pointer on-off"
                        
; LED strings ---------------------------------------------------------
bstr_ledf:
                        .sdataz "LED filter"
bstr_leda:
                        .sdataz "LED absolute-relative"
bstr_led_speed:
                        .sdataz "LED speed"
bstr_hold:
                        .sdataz "Hold LED bearing"
bstr_dim:
                        .sdataz "Dim LED"
                        
; ---------------------------------------------------------------------
;
bstr_attract:
                        .sdataz "Toggle LED attract display"
bstr_calibrate:
                        .sdataz "Set calibration values"
bstr_check_antenna:
                        .sdataz "Check antenna switch"
bstr_config:
                        .sdataz "Switch active configuration"
bstr_save:
                        .sdataz "Save current configuration"
bstr_rot:
                        .sdataz "Change antenna rotation rate"
bstr_accept:
                        .sdataz "Save calibration values"
bstr_threshold:
			.sdataz "Change Q threshold"
bstr_sample_size:
			.sdataz "Set filter sample size"
bstr_lcd_ab:
                        .sdataz "LCD absolute filter"
bstr_lcd_rel:
                        .sdataz "LCD relative filter"
bstr_custom_1:
                        .sdataz "Print `CB1`"
bstr_custom_2:
                        .sdataz "Print `CB2`"
bstr_custom_3:
                        .sdataz "Print `CB3`"
bstr_custom_4:
                        .sdataz "Print `CB4`"
bstr_func_1:
                        .sdataz "CB1"
bstr_func_2:
                        .sdataz "CB2"
bstr_func_3:
                        .sdataz "CB3"
bstr_func_4:
                        .sdataz "CB4"

; *******************************************************************
;
;       EEPROM defaults here
;       Load them into RAM first so if EEprom missing
;       Real data loaded from EEprom to RAM
;
; *******************************************************************
;
                .res.b  h'2e            ; Manual set for debug to
                .data.w 1               ; keep eeprom image on even boundry
;
eeprom_image:
                .data.w h'f003          ; ver_number
;       init_processes
                .data.b 1               ; ps_serial_in          on
                .data.b 2		; ps_lcd		sleep
                
                .data.b 1               ; ps_buttin             on
                .data.b 0               ; ps_attractor
                
                .data.b 1               ; ps_led_ring_display   on
                .data.b 0               ; ps_aprs_snooper
                
                .data.b 1               ; ps_analog             on
                .data.b 1               ; ps_dial_out           on
                
                .data.b 1               ; ps_stepper_driver     on
                .data.b 1               ; ps_led_driver         on
                
                .data.b 0               ; ps_calibrate
                .data.b 1               ; ps_alarm              on
                
                .data.b 0               ; ps_sound_driver
                .data.b 0


FUNC_NOTHING:                   .EQU	h'00
FUNC_ATTRACT:                   .EQU	h'01
FUNC_CALIBRATE:                 .EQU	h'02
FUNC_ACCEPT_CAL:                .EQU	h'04
FUNC_APRS_SNOOP:                .EQU	h'05
FUNC_PTR_ON_OFF:                .EQU	h'06
FUNC_ROT:                       .EQU	h'07
FUNC_HOLD:                      .EQU	h'09
FUNC_SAMPLE_SIZE                .EQU	h'0A
FUNC_THRESHOLD                  .EQU	h'0B
FUNC_BEARING:                   .EQU	h'0C
FUNC_GPS:                       .EQU	h'0E
FUNC_CONFIG:                    .EQU	h'0F
FUNC_CHECK_ANTENNA:             .EQU	h'10
FUNC_DIM_LED:                   .EQU	h'11
FUNC_BEARING_N_GPS:             .EQU	h'12
FUNC_SAVE:                      .EQU	h'13
FUNC_PTR_SPEED:                 .EQU	h'03
FUNC_LED_SPEED:                 .EQU	h'0D
FUNC_PTR_FILT                   .EQU	h'14
FUNC_LED_FILT                   .EQU	h'15
FUNC_PTR_ABS                    .EQU	h'16
FUNC_LED_ABS                    .EQU	h'17
FUNC_LCD_A			.EQU	h'18
FUNC_LCD_R			.EQU	h'19


FUNC_CUST_1:                    .EQU	h'71
FUNC_CUST_2:                    .EQU	h'72
FUNC_CUST_3:                    .EQU	h'73
FUNC_CUST_4:                    .EQU	h'74
;

;       Button function assignments (button function codes)
                .data.b FUNC_LED_FILT           ; button_1
                .data.b FUNC_LED_ABS            ; button_2

                .data.b FUNC_LED_SPEED          ; button_3
                .data.b FUNC_ROT                ; button_4

                .data.b FUNC_THRESHOLD          ; button_5
                .data.b FUNC_LCD_A              ; button_6

                .data.b FUNC_LCD_R              ; button_7
                .data.b FUNC_CHECK_ANTENNA      ; button_8

                .data.b FUNC_PTR_FILT           ; button_9  hold down of button 1
                .data.b FUNC_PTR_ABS            ; button_10 hold down of button 2

                .data.b FUNC_PTR_SPEED          ; button_11 hold down of button 3
                .data.b FUNC_HOLD               ; button_12 hold down of button 4

                .data.b FUNC_SAMPLE_SIZE        ; button_13 hold down of button 5
                .data.b FUNC_CONFIG             ; button_14 hold down of button 6

                .data.b FUNC_CALIBRATE		; button_15 hold down of button 7
                .data.b FUNC_SAVE               ; button_16 hold down of button 8
                                                ; 30 bytes

;       This value block needs to be even boundary aligned These vairables are shadows,
;       used mainly in the ISR and should be considered read only.
;       They will be refreshed when the configuration changes.


                .data.b 0               ; calibration
                .data.b 0               ; antenna_configuration

;       This is the table for the stored configurations
;       Structure               hi nibble                       low nibble
;       byte            0 = disabled 1 = enabled        1 yes  0 = no   cal values
;       byte            number of ants          1 high 0 = low

;       byte * 6 calibrations
;       PLAN ON 10: So add some more bytes

;       Total 6 words per config (12 bytes)
;       4 configs means 24 words total or 48 bytes
;
;config_1:
                .data.b h'11    ; enabled - cal val not set
                .data.b h'41    ; 4 ant  - 1 active high
                .data.b 18	; calibrate rot rate 0
                .data.b 26	; calibrate rot rate 1
                .data.b 37	; calibrate rot rate 2
                .data.b 44	; calibrate rot rate 3
                .data.b 50	; calibrate rot rate 4
                .data.b 55	; calibrate rot rate 5
                .data.b 61	; calibrate rot rate 6
                .data.b 66	; calibrate rot rate 7
                .data.b 72	; calibrate rot rate 8
                .data.b 79      ; calibrate rot rate 9
                .data.b 6       ; default rotation rate
;
;config_2:
                .data.b h'01    ; enabled - cal val not set
                .data.b h'61    ; 6 ant  - active high
                .data.b 0       ; calibrate rot rate 0
                .data.b 0       ; calibrate rot rate 1
                .data.b 0       ; calibrate rot rate 2
                .data.b 0       ; calibrate rot rate 3
                .data.b 0       ; calibrate rot rate 4
                .data.b 0       ; calibrate rot rate 5
                .data.b 0       ; calibrate rot rate 6
                .data.b 0       ; calibrate rot rate 7
                .data.b 0       ; calibrate rot rate 8
                .data.b 0       ; calibrate rot rate 9
                .data.b 0       ; default rotation rate
;
;config_3:
                .data.b h'01    ; enabled - cal val not set
                .data.b h'81    ; 8 ant  -  active high
                .data.b 0       ; calibrate rot rate 0
                .data.b 0       ; calibrate rot rate 1
                .data.b 0       ; calibrate rot rate 2
                .data.b 0       ; calibrate rot rate 3
                .data.b 0       ; calibrate rot rate 4
                .data.b 0       ; calibrate rot rate 5
                .data.b 0       ; calibrate rot rate 6
                .data.b 0       ; calibrate rot rate 7
                .data.b 0       ; calibrate rot rate 8
                .data.b 0       ; calibrate rot rate 9
                .data.b 0       ; default rotation rate
;config_4:
                .data.b h'01    ; enabled - cal val not set
                .data.b h'41    ; 4 ant  - active high
                .data.b 0       ; calibrate rot rate 0
                .data.b 0       ; calibrate rot rate 1
                .data.b 0       ; calibrate rot rate 2
                .data.b 0       ; calibrate rot rate 3
                .data.b 0       ; calibrate rot rate 4
                .data.b 0       ; calibrate rot rate 5
                .data.b 0       ; calibrate rot rate 6
                .data.b 0       ; calibrate rot rate 7
                .data.b 0       ; calibrate rot rate 8
                .data.b 0       ; calibrate rot rate 9
                .data.b 0       ; default rotation rate
        %IF KN6FW
                .sdataz "WB6YRU >"       ; str_prompt
;                .data.b 0
                .data.b 0 
 
        %ELSE 
                .sdataz "dop >"         ; str_prompt
                .data.b 0 
                .data.b 0 
                .data.b 0 
                .data.b 0               ; 90 bytes

        %ENDIF
                .data.b 0               ; current_rotation_rate
                .data.b 1               ; current_config

                .data.b 0               ; current_display
                .data.b 0               ; current_unknown
;display_address_table:
;
;       Which filter output is used by which display
;       filter output data address0 to ?data in table.
;
                .data.w data_4_leds     ; Data address 4 leds
                .data.w data_4_ptr      ; load with filt_x_output
                .data.w data_4_lcda	; lcd absolute bearing
                .data.w data_4_lcdr	; lcd relative bearing
                .data.w data_4_serial
                .data.w data_4_lrtone
;
                .data.b 0               ; current_ptr_filter
                .data.b 0               ; current_led_filter
                .data.b 0		; current_lcda_filter
                .data.b 0		; current_lcdr_filter
                .data.b 0		; current_serial_filter
                .data.b 0		; current_lrtone_filter
;
                .data.b 0               ; spare
                .data.b BIT_RATE_4800   ; serial_rate1
                                

                .data.b BIT_RATE_4800   ; serial_rate
                .data.b 0               ; snooper_qlevel

                .data.b 244             ; antenna_voltage_too_high_d244
                .data.b 15              ; antenna_voltage_too_low_d15

                .data.b 14              ; antenna_voltage_same_delta_d14
                .data.b 10              ; GPS_min_speed
 
                .data.w 20              ; doppler_qual_threshold
                .data.w 0               ; snooper_constant
                .data.w 10              ; lost_alarm_time
                .data.w 0               ; pointer_delay


;       ctrl - option bytes
;       These can be tested with a mov.b to any register
;       They can be changed with        mov.w   #ctrl_byte_xxx,rx
;                                       bxor    #0,@rx

;       0 equal off or inactive
;       1 equal on  or active


                .data.b 0               ; GPS_capture_flag:
                .data.b 0               ; GPS_capture_flag_SNOOP_PENDING:
;
                .data.b 0               ; GPS_echo_flag:
                .data.b 0               ; ctrl_byte_APRS_LIMIT:
;
                .data.b 0               ; ctrl_byte_Old_APRS_compat:
                .data.b 0               ; ctrl_byte_Snoop_pending:
;
                .data.b 1               ; current_Threshold
                .data.b 1               ; ctrl_byte_Start_tone:
;
                .data.b 0               ; ctrl_byte_Button_click:
                .data.b 1               ; ctrl_byte_Pointer_avail:
;
                .data.b 0               ; pointer_abs_flag:
                .data.b 0               ; LED_abs_flag:
;
                .data.b 0               ; ctrl_byte_Dim_LED:
                .data.b 0               ; ctrl_byte_BEARING_FORCE_SNOOP:
;
		.res.b  1		; bearing_print_flag:
					; Which of the 4 LED  
					; displays will filter
					; display on
;
 		.data.b  1		; LED8_out_RED:	
;
		.data.b  2		; LED8_out_GREEN:
		.data.b  3		; LED8_iner_RED:
;
		.data.b  4		; LED8_iner_GREEN:
		.data.b  0		; spare
;
eeprom_image_end:
eeprom_image_size:              .equ    eeprom_image_end - eeprom_image

; ************************ End of EEPROM defaults ***********************


end_str:                        .data.w h'dead
                        	.data.w h'beef



fence_string_end:
;
; ****** RAM ****** RAM ****** RAM ****** RAM ****** RAM ****** RAM ******
;
;        %IF DEVELOP_ASM
;        .section        RAM, DATA,LOCATE=h'5780     ; Allows Logic analyzer read
;        %ELSE
        .section        RAM, DATA,LOCATE=h'f780     ; On Chip RAM
;        %ENDIF
fence_ram_start:

led_delay:                      .res.w  1

pointer_state:                  .res.w  1

;       Delay to let system settle in until we grab a calibration value

calibration_timer:              .res.w  1

;       Delay initialization constant

pointer_location:               .res.w  1
pointer_target:                 .res.w  1

;       Time the blinks for primary LED
;       Non-critical variable. Does not need initializartion.

led_blink_timer:                .res.w  1

;       The current amount of time to wait before updating
;       the led ring. A process state timer.

led_delay_time_value:           .res.w  1

;       Point to current pattern for 7 segment display

led_7seg_pattern:               .res.w  1

led_target:                     .res.w  1

;       This can be used for a variety of LOCAL purposes

temporary:                      .res.w  1
temp_rot_value:			.res.w	1

;       Mode switches to change some behavior.

maintenance_mode:               .res.w  1
;
filt_3_average_b		.res.b	1
filt_3_bad_cnt			.res.b	1
filt_3_new_b			.res.b	1
filt_3_sample_cnt		.res.b	1
filt_3_ave_total		.res.w	1
;
Bearing_sum:			.res.w	1
q_sum:				.res.b	2
;
filt_0_output:                  .res.w  1
filt_1_output:                  .res.w  1
filt_2_output:                  .res.w  1
filt_3_output:                  .res.w  1
filt_4_output:			.res.w	1
filt_5_output:			.res.w	1

;
filt_0_A_output:                .res.w  1
filt_1_A_output:                .res.w  1
filt_2_A_output:                .res.w  1
filt_3_A_output:                .res.w  1
filt_4_A_output:                .res.w  1
filt_5_A_output:                .res.w  1
;
max_filter:			.equ	(filt_5_output - filt_0_output)
;
;       This bucket aligns bearing with quality
qsync_bucket_full_flag          .res.b  1
qsync_bearing                   .res.b  1

qsync_bucket_ptr:               .res.w  1
qsync_bucket_end:               .res.w  1
qsync_bucket_mem_start:         .res.b  120


;       This is a real time clock time, in uSeconds since
;       startup. I think this will allow for a 7 year time.

rt_clock_sec_change_flag:       .res.w  1
rt_clock_mS_change:             .res.w  1
rt_clock_hour:                  .res.w  1       ; binary        0 ->
rt_clock_min:                   .res.b  1       ; byte  "       0 - 59
rt_clock_sec:                   .res.b  1       ; byte  "       0 - 59
rt_clock_msec:                  .res.w  1       ; word  "       0 - 999
rt_clock_usec:                  .res.w  1       ; word  "       0 - 999


;       Real time software timers

rt_sec_alarm:                   .res.w  1
rt_sec_snooper:                 .res.w  1
rt_sec_init:			.res.w  1
rt_sec_gps:                     .res.w  1
rt_sec_uart_turn_on:		.res.w  1
rt_msec_sounder:                .res.w  1
rt_msec_marquee:                .res.w  1
rt_msec_attractor:              .res.w  1
rt_msec_stepper:                .res.w  1
rt_msec_alarm_process:          .res.w  1
rt_msec_lcd			.res.w  1
rt_msec_led_ring_process:       .res.w  1
rt_msec_but_2nd:                .res.w  1
rt_msec_ant_chk:                .res.w  1

real_time_quantum:              .res.w  1

gps_speed:                	.res.w  1
gps_bearing:                    .res.w  1
gps_retain_time:                .res.w  1

ant_chk_pointer:                .res.w  1

stack_sniffer:                  .res.w  1

; *********************************************************

;       This is an image of the EEPROM
;       The EEPROM gets read in here.
;       If it can not be read or is not read the defaults
;       are read from program PROM.
;       Actually the PROM image is moved here first
;       then over-written by the EEPROM

;       Byte values welcome here
;       NOT REALY must be in pairs

;       Process state values
;       NOTE These entries must be aligned on even boundaries
;       so the eesave routine will work correctly.
;       there has to be an even number of entries.

; *********************************************************
        %IF DEVELOP_ASM
        .section eestore, DATA,LOCATE=$+h'100&h'ff00 ; h'f900
        %ENDIF
;       makes it easier to debug
;
; ****** EEPROM DATA RAM ****** EEPROM DATA RAM ****** EEPROM DATA RAM *****
;eeprom_image:
;process_state_table:
eeprom_ram_start:

ver_number:                     .res.w  1

ps_serial_in:                   .res.b  1
ps_lcd:				.res.b  1

ps_buttin:                      .res.b  1
ps_attractor:                   .res.b  1

ps_led_ring_display:            .res.b  1
ps_aprs_snooper:                .res.b  1

ps_analog:                      .res.b  1
ps_dial_out:                    .res.b  1

ps_stepper_driver:              .res.b  1
ps_led_driver:                  .res.b  1

ps_calibrate:                   .res.b  1
ps_alarm:                       .res.b  1

ps_sound_driver:                .res.b  1
				.res.b  1

;       Button function assignments (button function codes)

button_1_function:              .res.b  1
button_2_function:              .res.b  1
button_3_function:              .res.b  1
button_4_function:              .res.b  1
button_5_function:              .res.b  1
button_6_function:              .res.b  1
button_7_function:              .res.b  1
button_8_function:              .res.b  1
button_9_function:              .res.b  1
button_10_function:             .res.b  1
button_11_function:             .res.b  1
button_12_function:             .res.b  1
button_13_function:             .res.b  1
button_14_function:             .res.b  1
button_15_function:             .res.b  1
button_16_function:             .res.b  1

;       This value block needs to be even boundary aligned
;       These vairables are shadows, used mainly in the ISR
;       and should be considered read only.
;       They will be refreshed when the configuration changes.


calibration:                    .res.b  1
antenna_configuration:          .res.b  1

;       This is the table for the stored configurations
;       Structure ==
;       byte * 1 active.enabled (hi nibble, lo nibble)
;       byte * 1 antenna config
;       byte * 10 calibrations (only need 5, but have to be aligned.)
;
;       Total 6 words per config (12 bytes)
;       4 configs means 24 words total

config_1:                   .res.b  13
;                .data.b h'11    ; enabled - cal val not set
;                .data.b h'41    ; 4 ant  - 1 active high
;                .data.b 134     ; calibrate rot rate 0
;                .data.b 140     ; calibrate rot rate 1
;                .data.b 146     ; calibrate rot rate 2
;                .data.b 30      ; calibrate rot rate 3
;                .data.b 40      ; calibrate rot rate 4
;                .data.b 50      ; calibrate rot rate 5
;                .data.b 60      ; calibrate rot rate 6
;                .data.b 70      ; calibrate rot rate 7
;                .data.b 80      ; calibrate rot rate 8
;                .data.b 90      ; calibrate rot rate 9
;                .data.b 5       ; default rotation rate
;
config_2:                   .res.b  13
;                .data.b h'11    ; enabled - cal val not set
;                .data.b h'41    ; 4 ant  - 1 active high
;                .data.b 134     ; calibrate rot rate 0
;                .data.b 140     ; calibrate rot rate 1
;                .data.b 146     ; calibrate rot rate 2
;                .data.b 30      ; calibrate rot rate 3
;                .data.b 40      ; calibrate rot rate 4
;                .data.b 50      ; calibrate rot rate 5
;                .data.b 60      ; calibrate rot rate 6
;                .data.b 70      ; calibrate rot rate 7
;                .data.b 80      ; calibrate rot rate 8
;                .data.b 90      ; calibrate rot rate 9
;                .data.b 5       ; default rotation rate
config_3:                   .res.b  13
;                .data.b h'11    ; enabled - cal val not set
;                .data.b h'41    ; 4 ant  - 1 active high
;                .data.b 134     ; calibrate rot rate 0
;                .data.b 140     ; calibrate rot rate 1
;                .data.b 146     ; calibrate rot rate 2
;                .data.b 30      ; calibrate rot rate 3
;                .data.b 40      ; calibrate rot rate 4
;                .data.b 50      ; calibrate rot rate 5
;                .data.b 60      ; calibrate rot rate 6
;                .data.b 70      ; calibrate rot rate 7
;                .data.b 80      ; calibrate rot rate 8
;                .data.b 90      ; calibrate rot rate 9
;                .data.b 5       ; default rotation rate
;
config_4:                   .res.b  13
;                .data.b h'11    ; enabled - cal val not set
;                .data.b h'41    ; 4 ant  - 1 active high
;                .data.b 134     ; calibrate rot rate 0
;                .data.b 140     ; calibrate rot rate 1
;                .data.b 146     ; calibrate rot rate 2
;                .data.b 30      ; calibrate rot rate 3
;                .data.b 40      ; calibrate rot rate 4
;                .data.b 50      ; calibrate rot rate 5
;                .data.b 60      ; calibrate rot rate 6
;                .data.b 70      ; calibrate rot rate 7
;                .data.b 80      ; calibrate rot rate 8
;                .data.b 90      ; calibrate rot rate 9
;                .data.b 5       ; default rotation rate

;
;       Character array, but must be word aligned.
str_prompt:                     .res.b  10


current_rotation_rate:          .res.b  1
current_config:                 .res.b  1 
current_display:                .res.b  1
current_unknown:                .res.b  1

display_address_table:
;       Which filter output is used by which display
;       filter output data address0 to ?data in table.
data_4_leds:                    .res.w  1       ; Data address 4 leds
data_4_ptr:                     .res.w  1       ; load with filt_x_output
data_4_lcda:			.res.w  1       ; lcd absolute bearing
data_4_lcdr:			.res.w	1	; lcd relative bearing
data_4_serial:                  .res.w  1
data_4_lrtone:                  .res.w  1

current_led_filter:             .res.b  1
current_ptr_filter:             .res.b  1
current_lcda_filter:		.res.b	1
current_lcdr_filter:		.res.b	1
current_serial_filter:		.res.b	1
current_lrtone_filter:		.res.b	1

serial_rate:                    .res.b  1
snooper_qlevel:                 .res.b  1

spare:				.res.b  1
serial_rate1:                   .res.b  1

antenna_voltage_too_high_d244:  .res.b  1
antenna_voltage_too_low_d15:    .res.b  1

antenna_voltage_same_delta_d14: .res.b  1
GPS_min_speed:            	.res.b  1

doppler_qual_threshold:         .res.w  1
snooper_constant:               .res.w  1
lost_alarm_time:                .res.w  1
pointer_delay:                  .res.w  1

GPS_capture_flag:               .res.b  1
GPS_capture_flag_SNOOP_PENDING: .res.b  1

GPS_echo_flag:        		.res.b  1
ctrl_byte_APRS_LIMIT:           .res.b  1

ctrl_byte_Old_APRS_compat:      .res.b  1
ctrl_byte_Snoop_pending:        .res.b  1

current_Threshold:		.res.b  1
ctrl_byte_Start_tone:           .res.b  1

ctrl_byte_Button_click:         .res.b  1
ctrl_byte_Pointer_avail:        .res.b  1

pointer_abs_flag:               .res.b  1
LED_abs_flag:                   .res.b  1

ctrl_byte_Dim_LED:              .res.b  1
ctrl_byte_BEARING_FORCE_SNOOP:  .res.b  1

bearing_print_flag:             .res.b  1
LED8_out_RED:			.res.b  1	; Which filter  
						; witch display
LED8_out_GREEN:			.res.b  1
LED8_iner_RED:			.res.b  1
				
LED8_iner_GREEN:		.res.b  1
				.res.b  1								
				
eeprom_ram_end:
eeprom_ram_size:		.equ (eeprom_ram_end - eeprom_ram_start)
;
fillerlabel:
;
; ************************* End EEPROM RAM storage ******************
raw_store:			.res.w	1
gps_stop_flag			.res.b	1
gps_stop_qual			.res.b	1
ant_chk_volts:                  .res.b  16      ; status then voltage
eesave_ptr:			.res.w  1
cal_val_ptr			.res.w	1
dopp_qual_last:                 .res.b  1
ctrl_byte_PTT:                  .res.b  1
ctrl_byte_CHECK_ANTENNA:        .res.b  1
GPS_capture_flag_can_parse:     .res.b  1
ctrl_byte_Flush_GPS:            .res.b  1
ctrl_byte_hold:                 .res.b  1
				.res.b  1
ctrl_byte_stop_leds:            .res.b  1

analog_channel_2_data:          .res.b  1       ; Pin 2 on Power J1
analog_channel_3_data:          .res.b  1       ; Pin 3 on Power J1

;       5 items of DURATION/SOUND
sound_queue:                    .res.b  20

antenna_failure:                .res.b  1

missed_1_flag_max:              .res.b  1


;       .data.b hardware_version,1
hardware_version:               .res.b  1

;       Rev 0 board uses bit 4 for button detect
;       Rev 1 board uses bit 6 for button detect

hdw_button_bit:                 .res.b  1

but_debounce_flag:              .res.b  1
but_number_stor:                .res.b  1

;       Used in the attract mode.

led_id:                         .res.b  1
led_dir:                        .res.b  1
led_quadrant:                   .res.b  1

;       Led values from doppler, and filtered LED displays
;       Led Primary is a value in the circle.
;       Led Secondary is a value in the circle, or UNUSED
;       See also "led_7seg_pattern" ptrs

current_LED_speed:              .res.b  1
led_primary:                    .res.b  1
led_secondary:                  .res.b  1
led_disp_primary_flag:          .res.b  1
led_7_current_char:             .res.b  1
led_7_qbar:                     .res.b  1
led_7_seg_idx:                  .res.b  1
led_7_marquee:                  .res.b  MARQUEE_SIZE
led_7_marquee_length:           .res.b  1

;       .res.b  led_7_marquee_length,1

led_7_marquee_idx:              .res.b  1

;       Remember what the last direction we were traveling
;       so the stepper control can zero in the correct direction.


pointer_delay_idx:              .res.b  1
overlap_time:			.res.b	1

zero_info_direction:		.res.b	1
zero_info_reed_closed:		.res.b	1
pointer_target2:		.res.w	1

;       Doppler quality calculations

doppler_qual_raw:		.res.w  1
doppler_qual_fund1:             .res.w  1
doppler_qual_fund2:             .res.w  1
doppler_qual_fund3:             .res.w  1
doppler_qual_fund4:             .res.w  1
doppler_qual_fund:              .res.b  1
doppler_qual_fundx:             .res.b  1

doppler_qual_2nd:               .res.b  1
doppler_qual_0T9:		.res.b  1
doppler_qual_timer:             .res.b  1

good_Q_count:			.res.b  1
current_sample_size:		.res.b  1
current_sample_number:		.res.b  1
				.res.b  1
;
;		.data.b	h'8c,h'b8,h'80
;		.sdata  "C 555 An 444 Lrn"
;		.data.b	h'c0
;		.sdata  "R5 Q9 Rn 666 Prn"
;		.data.b	h'ff
;
lcd_line1:			.res.b	 3 ; h'81h'8c,h'b8,h'80 ;19
				.res.b	 1	; C
				.res.b	 1	; sp
lcd_comp:			.res.b   3
				.res.b	 1	; sp
				.res.b	 1	; A
lcd_afilt:			.res.b	 1
				.res.b	 1	; sp
lcd_abearing:			.res.b	 3
				.res.b	 1	; sp
				.res.b	 1	; L
lcd_led_state:			.res.b	 2
;
lcd_line2:			.res.b	 1 ; h'c0 ; 18
				.res.b	 1	; R
lcd_rot:			.res.b   1
				.res.b	 1	; sp
				.res.b	 1	; Q
lcd_qualty:			.res.b	 1
				.res.b	 1	; sp
lcd_R2:				.res.b	 1
lcd_rfilt:			.res.b	 1
				.res.b	 1	; sp
lcd_rbearing:			.res.b	 3
				.res.b	 1	; sp
				.res.b	 1	; P
lcd_pointer_state:		.res.b   2
				.res.b	 1 ; h'ff end flag
				
lcd_pointer:			.res.w	 1


gps_heading_dd:                 .res.b  1
gps_speed_flag:			.res.b  1


sound_length:                   .res.b  1
sound_position:                 .res.b  1

;       The input buffer being 80 characters is big
;       enough to handle GPS input strings.

inp_len:                        .res.b  1

inp_buf:                        .res.b  84
inp_buf_end:			.res.b	2		; just in case of overrun
inp_max:			.equ	(inp_buf_end - inp_buf)
out_buf:                        .res.b  10
 
out_buf_end:                    .res.b  2

;       All characters written are sent to this buffer and the
;       output processor takes care of emptying it.

output_buffer:                  .res.b  700		; Needed for long messages
output_buffer_end:              .res.w  1
output_buffer_in_ptr:           .res.w  1
output_buffer_Out_ptr:          .res.w  1

output_buffer2:                 .res.b  16
output_buffer2_end:             .res.w  1
output_buffer2_in_ptr:          .res.w  1
output_buffer2_out_ptr:         .res.w  1
;
Input_buffer2:			.res.b	82
Input_buffer2_ptr:		.res.w	1


;       If ant_one_flag = 0 don't do things required once per revolution
;       If ant_one_flag = 1 do it and then set it to zero
;       If ant_one_flag = 2 or more we missed something oops

ant_one_flag:                   .res.b  1
test_flag:                      .res.b  1
GPRMC_string_flag:		.res.b	1
GPRMC_Find_flag:		.res.b	1
last_sent_Q:			.res.b	1
Q_count:			.res.b	1
filter_rot			.res.b	1
				.res.b  1
;
LED8_out_odd:			.res.b	1
LED8_out_even:			.res.b	1
LED8_iner_odd:			.res.b	1
LED8_iner_even:			.res.b	1
FlipFlop:			.res.b  1
				
;       Queue filtering.

no_more:
fence_ram_end:

stack:                          .EQU    h'FF7E

        .END
