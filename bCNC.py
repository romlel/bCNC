#!/bin/python2
# -*- coding: ascii -*-

#This is loader script for bCNC, which can also be compiled to .exe

from __future__ import absolute_import
from __future__ import print_function
import os
import re
import sys
import pdb
import time
import getopt
import socket
import traceback
from datetime import datetime

try:
	import serial
except:
	serial = None

try:
	import Tkinter
	from Queue import *
	from Tkinter import *
	import ConfigParser
	import tkMessageBox
except ImportError:
	import tkinter
	from queue import *
	from tkinter import *
	import configparser as ConfigParser
	import tkinter.messagebox as tkMessageBox

PRGPATH=os.path.abspath(os.path.dirname(__file__))
sys.path.append(os.path.join(PRGPATH, 'lib'))
sys.path.append(os.path.join(PRGPATH, 'plugins'))

# Load configuration before anything else
# and if needed replace the  translate function _()
# before any string is initialized
import Utils
Utils.loadConfiguration()

import rexx
import tkExtra
import Unicode
import Updates
import bFileDialog

from CNC import WAIT, CNC, GCode
import Ribbon
import Pendant
from Sender import Sender, NOT_CONNECTED, STATECOLOR, STATECOLORDEF

import CNCList
import CNCCanvas
import webbrowser

from CNCRibbon	  import Page
from ToolsPage	  import Tools, ToolsPage
from FilePage	  import FilePage
from ControlPage  import ControlPage
from TerminalPage import TerminalPage
from ProbePage	  import ProbePage
from EditorPage   import EditorPage

_openserial = True	# override ini parameters
_device     = None
_baud	    = None

MONITOR_AFTER =  200	# ms
DRAW_AFTER    =  300	# ms

RX_BUFFER_SIZE = 128

MAX_HISTORY  = 500

#ZERO = ["G28", "G30", "G92"]

FILETYPES = [	(_("All accepted"), ("*.ngc","*.nc", "*.tap", "*.gcode", "*.dxf", "*.probe", "*.orient", "*.stl")),
		(_("G-Code"),("*.ngc","*.nc", "*.tap", "*.gcode")),
		(_("G-Code clean"),("*.txt")),
		("DXF",       "*.dxf"),
		("SVG",       "*.svg"),
		(_("Probe"),  "*.probe"),
		(_("Orient"), "*.orient"),
		("STL",       "*.stl"),
		(_("All"),    "*")]

geometry = None

#==============================================================================
# Main Application window
#==============================================================================
class Application(Toplevel,Sender):
	def __init__(self, master, **kw):
		Toplevel.__init__(self, master, **kw)
		Sender.__init__(self)

		if sys.platform == "win32":
			self.iconbitmap("bCNC.ico")
		else:
			self.iconbitmap("@%s/bCNC.xbm"%(Utils.prgpath))
		self.title(Utils.__prg__)
		self.widgets = []

		# Global variables
		self.tools = Tools(self.gcode)
		self.loadConfig()

		# --- Ribbon ---
		self.ribbon = Ribbon.TabRibbonFrame(self)
		self.ribbon.pack(side=TOP, fill=X)

		# Main frame
		self.paned = PanedWindow(self, orient=HORIZONTAL)
		self.paned.pack(fill=BOTH, expand=YES)

		# Status bar
		frame = Frame(self)
		frame.pack(side=BOTTOM, fill=X)
		self.statusbar = tkExtra.ProgressBar(frame, height=20, relief=SUNKEN)
		self.statusbar.pack(side=LEFT, fill=X, expand=YES)
		self.statusbar.configText(fill="DarkBlue", justify=LEFT, anchor=W)

		self.statusz = Label(frame, foreground="DarkRed", relief=SUNKEN, anchor=W, width=10)
		self.statusz.pack(side=RIGHT)
		self.statusy = Label(frame, foreground="DarkRed", relief=SUNKEN, anchor=W, width=10)
		self.statusy.pack(side=RIGHT)
		self.statusx = Label(frame, foreground="DarkRed", relief=SUNKEN, anchor=W, width=10)
		self.statusx.pack(side=RIGHT)

		# Buffer bar
		self.bufferbar = tkExtra.ProgressBar(frame, height=20, width=40, relief=SUNKEN)
		self.bufferbar.pack(side=RIGHT, expand=NO)
		self.bufferbar.setLimits(0, 100)
		tkExtra.Balloon.set(self.bufferbar,_("Controller buffer fill"))

		# --- Left side ---
		frame = Frame(self.paned)
		self.paned.add(frame) #, minsize=340)

		pageframe = Frame(frame)
		pageframe.pack(side=TOP, expand=YES, fill=BOTH)
		self.ribbon.setPageFrame(pageframe)

		# Command bar
		f = Frame(frame)
		f.pack(side=BOTTOM, fill=X)
		self.cmdlabel = Label(f, text=_("Command:"))
		self.cmdlabel.pack(side=LEFT)
		self.command = Entry(f, relief=SUNKEN, background="White")
		self.command.pack(side=RIGHT, fill=X, expand=YES)
		self.command.bind("<Return>",		self.cmdExecute)
		self.command.bind("<Up>",		self.commandHistoryUp)
		self.command.bind("<Down>",		self.commandHistoryDown)
		self.command.bind("<FocusIn>",		self.commandFocusIn)
		self.command.bind("<FocusOut>",		self.commandFocusOut)
		self.command.bind("<Key>",		self.commandKey)
		self.command.bind("<Control-Key-z>",	self.undo)
		self.command.bind("<Control-Key-Z>",	self.redo)
		self.command.bind("<Control-Key-y>",	self.redo)
		tkExtra.Balloon.set(self.command,
			_("MDI Command line: Accept g-code commands or macro " \
			  "commands (RESET/HOME...) or editor commands " \
			  "(move,inkscape, round...) [Space or Ctrl-Space]"))
		self.widgets.append(self.command)

		# --- Right side ---
		frame = Frame(self.paned)
		self.paned.add(frame)

		# --- Canvas ---
		self.canvasFrame = CNCCanvas.CanvasFrame(frame, self)
		self.canvasFrame.pack(side=TOP, fill=BOTH, expand=YES)
		#self.paned.add(self.canvasFrame)
# XXX FIXME do I need the self.canvas?
		self.canvas = self.canvasFrame.canvas

		# fist create Pages
		self.pages = {}
		for cls in (	ControlPage,
				EditorPage,
				FilePage,
				ProbePage,
				TerminalPage,
				ToolsPage):
			page = cls(self.ribbon, self)
			self.pages[page.name] = page

		# then add their properties (in separate loop)
		errors = []
		for name,page in self.pages.items():
			for n in Utils.getStr(Utils.__prg__,"%s.ribbon"%(page.name)).split():
				try:
					page.addRibbonGroup(n)
				except KeyError:
					errors.append(n)

			for n in Utils.getStr(Utils.__prg__,"%s.page"%(page.name)).split():
				last = n[-1]
				try:
					if last == "*":
						page.addPageFrame(n[:-1],fill=BOTH,expand=TRUE)
					else:
						page.addPageFrame(n)
				except KeyError:
					errors.append(n)

		if errors:
			tkMessageBox.showwarning("bCNC configuration",
					"The following pages \"%s\" are found in your " \
					"${HOME}/.bCNC initialization " \
					"file, which are either spelled wrongly or " \
					"no longer exist in bCNC"%(" ".join(errors)),parent=self)

		# remember the editor list widget
		self.dro      = Page.frames["DRO"]
		self.gstate   = Page.frames["State"]
		self.control  = Page.frames["Control"]
		self.editor   = Page.frames["Editor"].editor
		self.terminal = Page.frames["Terminal"].terminal
		self.buffer   = Page.frames["Terminal"].buffer

		# XXX FIXME Do we need it or I can takes from Page every time?
		self.autolevel = Page.frames["Probe:Autolevel"]

		# Left side
		for name in Utils.getStr(Utils.__prg__,"ribbon").split():
			last = name[-1]
			if last == '>':
				name = name[:-1]
				side = RIGHT
			else:
				side = LEFT
			self.ribbon.addPage(self.pages[name],side)

		# Restore last page
		self.pages["Probe"].tabChange()	# Select "Probe:Probe" tab to show the dialogs!
		self.ribbon.changePage(Utils.getStr(Utils.__prg__,"page", "File"))

		probe = Page.frames["Probe:Probe"]
		tkExtra.bindEventData(self, "<<OrientSelect>>", lambda e,f=probe: f.selectMarker(int(e.data)))
		tkExtra.bindEventData(self, '<<OrientChange>>',	lambda e,s=self: s.canvas.orientChange(int(e.data)))
		self.bind('<<OrientUpdate>>',	probe.orientUpdate)

		# Global bindings
		self.bind('<<Undo>>',		self.undo)
		self.bind('<<Redo>>',		self.redo)
		self.bind('<<Copy>>',		self.copy)
		self.bind('<<Cut>>',		self.cut)
		self.bind('<<Paste>>',		self.paste)

		self.bind('<<Connect>>',	self.openClose)

		self.bind('<<New>>',		self.newFile)
		self.bind('<<Open>>',		self.loadDialog)
		self.bind('<<Save>>',		self.saveAll)
		self.bind('<<SaveAs>>',		self.saveDialog)
		self.bind('<<Reload>>',		self.reload)

		self.bind('<<Recent0>>',	self._loadRecent0)
		self.bind('<<Recent1>>',	self._loadRecent1)
		self.bind('<<Recent2>>',	self._loadRecent2)
		self.bind('<<Recent3>>',	self._loadRecent3)
		self.bind('<<Recent4>>',	self._loadRecent4)
		self.bind('<<Recent5>>',	self._loadRecent5)
		self.bind('<<Recent6>>',	self._loadRecent6)
		self.bind('<<Recent7>>',	self._loadRecent7)
		self.bind('<<Recent8>>',	self._loadRecent8)
		self.bind('<<Recent9>>',	self._loadRecent9)

		self.bind('<<TerminalClear>>',	Page.frames["Terminal"].clear)
		self.bind('<<AlarmClear>>',	self.alarmClear)
		self.bind('<<Help>>',		self.help)
						# Do not send the event otherwise it will skip the feedHold/resume
		self.bind('<<FeedHold>>',	lambda e,s=self: s.feedHold())
		self.bind('<<Resume>>',		lambda e,s=self: s.resume())
		self.bind('<<Run>>',		lambda e,s=self: s.run())
		self.bind('<<Stop>>',		self.stopRun)
		self.bind('<<Pause>>',		self.pause)
#		self.bind('<<TabAdded>>',	self.tabAdded)

		tkExtra.bindEventData(self, "<<Status>>",	self.updateStatus)
		tkExtra.bindEventData(self, "<<Coords>>",	self.updateCanvasCoords)

		# Editor bindings
		self.bind("<<Add>>",			self.editor.insertItem)
		self.bind("<<Clone>>",			self.editor.clone)
		self.canvas.bind("<Control-Key-Prior>",	self.editor.orderUp)
		self.canvas.bind("<Control-Key-Next>",	self.editor.orderDown)
		self.canvas.bind('<Control-Key-d>',	self.editor.clone)
		self.canvas.bind('<Control-Key-c>',	self.copy)
		self.canvas.bind('<Control-Key-x>',	self.cut)
		self.canvas.bind('<Control-Key-v>',	self.paste)
		self.bind("<<Delete>>",			self.editor.deleteBlock)
		self.canvas.bind("<Delete>",		self.editor.deleteBlock)
		self.canvas.bind("<BackSpace>",		self.editor.deleteBlock)
		try:
			self.canvas.bind("<KP_Delete>",	self.editor.deleteBlock)
		except:
			pass
		self.bind('<<Invert>>',		self.editor.invertBlocks)
		self.bind('<<Expand>>',		self.editor.toggleExpand)
		self.bind('<<EnableToggle>>',	self.editor.toggleEnable)
		self.bind('<<Enable>>',		self.editor.enable)
		self.bind('<<Disable>>',	self.editor.disable)
		self.bind('<<ChangeColor>>',    self.editor.changeColor)

		# Canvas X-bindings
		self.bind("<<ViewChange>>",	self.viewChange)
		self.bind("<<AddMarker>>",	self.canvas.setActionAddMarker)
		self.bind('<<MoveGantry>>',	self.canvas.setActionGantry)
		self.bind('<<SetWPOS>>',	self.canvas.setActionWPOS)

		frame = Page.frames["Probe:Tool"]
		self.bind('<<ToolCalibrate>>',	frame.calibrate)
		self.bind('<<ToolChange>>',	frame.change)

		self.bind('<<AutolevelMargins>>',self.autolevel.getMargins)
		self.bind('<<AutolevelZero>>',	self.autolevel.setZero)
		self.bind('<<AutolevelClear>>',	self.autolevel.clear)
		self.bind('<<AutolevelScan>>',	self.autolevel.scan)

		self.bind('<<CameraOn>>',	self.canvas.cameraOn)
		self.bind('<<CameraOff>>',	self.canvas.cameraOff)

		self.bind('<<CanvasFocus>>',	self.canvasFocus)
		self.bind('<<Draw>>',		self.draw)
		self.bind('<<DrawProbe>>',	lambda e,c=self.canvasFrame:c.drawProbe(True))
		self.bind('<<DrawOrient>>',	self.canvas.drawOrient)

		self.bind("<<ListboxSelect>>",	self.selectionChange)
		self.bind("<<Modified>>",	self.drawAfter)

		self.bind('<Control-Key-a>',	self.selectAll)
		self.bind('<Control-Key-A>',	self.unselectAll)
		self.bind('<Escape>',		self.unselectAll)
		self.bind('<Control-Key-i>',	self.selectInvert)

		self.bind('<<SelectAll>>',	self.selectAll)
		self.bind('<<SelectNone>>',	self.unselectAll)
		self.bind('<<SelectInvert>>',	self.selectInvert)
		self.bind('<<SelectLayer>>',	self.selectLayer)

#		self.bind('<Control-Key-f>',	self.find)
#		self.bind('<Control-Key-g>',	self.findNext)
#		self.bind('<Control-Key-h>',	self.replace)
		self.bind('<Control-Key-e>',	self.editor.toggleExpand)
		self.bind('<Control-Key-n>',	self.showInfo)
		self.bind('<<ShowInfo>>',	self.showInfo)
		self.bind('<Control-Key-l>',	self.editor.toggleEnable)
		self.bind('<Control-Key-q>',	self.quit)
		self.bind('<Control-Key-o>',	self.loadDialog)
		self.bind('<Control-Key-r>',	self.drawAfter)
		self.bind("<Control-Key-s>",	self.saveAll)
		self.bind('<Control-Key-y>',	self.redo)
		self.bind('<Control-Key-z>',	self.undo)
		self.bind('<Control-Key-Z>',	self.redo)
		self.canvas.bind('<Key-space>',	self.commandFocus)
		self.bind('<Control-Key-space>',self.commandFocus)
		self.bind('<<CommandFocus>>',	self.commandFocus)

		tools = self.pages["Tools"]
		self.bind('<<ToolAdd>>',	tools.add)
		self.bind('<<ToolDelete>>',	tools.delete)
		self.bind('<<ToolClone>>',	tools.clone)
		self.bind('<<ToolRename>>',	tools.rename)

		# self.bind('<Home>',		self.home)
		self.bind('<Prior>',		self.control.moveZup)
		self.bind('<Next>',		self.control.moveZdown)

		if self._swapKeyboard == 1:
			self.bind('<Right>',		self.control.moveYup)
			self.bind('<Left>',		self.control.moveYdown)
			self.bind('<Up>',		self.control.moveXdown)
			self.bind('<Down>',		self.control.moveXup)
		elif self._swapKeyboard == -1:
			self.bind('<Right>',		self.control.moveYdown)
			self.bind('<Left>',		self.control.moveYup)
			self.bind('<Up>',		self.control.moveXup)
			self.bind('<Down>',		self.control.moveXdown)
		else:
			self.bind('<Right>',		self.control.moveXup)
			self.bind('<Left>',		self.control.moveXdown)
			self.bind('<Up>',		self.control.moveYup)
			self.bind('<Down>',		self.control.moveYdown)

		try:
			self.bind('<KP_Home>',	self.home)
			self.bind('<KP_End>',	self.control.go2origin)
			self.bind('<KP_Prior>',	self.control.moveZup)
			self.bind('<KP_Next>',	self.control.moveZdown)

			if self._swapKeyboard==1:
				self.bind('<KP_Right>',	self.control.moveYup)
				self.bind('<KP_Left>',	self.control.moveYdown)
				self.bind('<KP_Up>',	self.control.moveXdown)
				self.bind('<KP_Down>',	self.control.moveXup)
			elif self._swapKeyboard==-1:
				self.bind('<KP_Right>',	self.control.moveYdown)
				self.bind('<KP_Left>',	self.control.moveYup)
				self.bind('<KP_Up>',	self.control.moveXup)
				self.bind('<KP_Down>',	self.control.moveXdown)
			else:
				self.bind('<KP_Right>',	self.control.moveXup)
				self.bind('<KP_Left>',	self.control.moveXdown)
				self.bind('<KP_Up>',	self.control.moveYup)
				self.bind('<KP_Down>',	self.control.moveYdown)
		except TclError:
			pass

		self.bind('<Key-plus>',		self.control.incStep)
		self.bind('<Key-equal>',	self.control.incStep)
		self.bind('<KP_Add>',		self.control.incStep)
		self.bind('<Key-minus>',	self.control.decStep)
		self.bind('<Key-underscore>',	self.control.decStep)
		self.bind('<KP_Subtract>',	self.control.decStep)

		self.bind('<Key-asterisk>',	self.control.mulStep)
		self.bind('<KP_Multiply>',	self.control.mulStep)
		self.bind('<Key-slash>',	self.control.divStep)
		self.bind('<KP_Divide>',	self.control.divStep)

		self.bind('<Key-1>',		self.control.setStep1)
		self.bind('<Key-2>',		self.control.setStep2)
		self.bind('<Key-3>',		self.control.setStep3)

		self.bind('<Key-exclam>',	self.feedHold)
		self.bind('<Key-asciitilde>',	self.resume)

		for x in self.widgets:
			if isinstance(x,Entry):
				x.bind("<Escape>", self.canvasFocus)

		self.bind('<FocusIn>',		self.focusIn)
		self.protocol("WM_DELETE_WINDOW", self.quit)

		self.canvas.focus_set()

		# Fill basic global variables
		CNC.vars["state"] = NOT_CONNECTED
		CNC.vars["color"] = STATECOLOR[NOT_CONNECTED]
		self._pendantFileUploaded = None
		self._drawAfter = None	# after handle for modification
		self._inFocus	= False
		self._insertCount = 0	# END - insertCount lines where ok was applied to for $xxx commands
		self.monitorSerial()
		self.canvasFrame.toggleDrawFlag()

		self.paned.sash_place(0, Utils.getInt(Utils.__prg__, "sash", 340), 0)

		# Auto start pendant and serial
		if Utils.getBool("Connection","pendant"):
			self.startPendant(False)

		if _openserial and Utils.getBool("Connection","openserial"):
			self.openClose()

		# Filedialog Load history
		for i in range(Utils._maxRecent):
			filename = Utils.getRecent(i)
			if filename is None: break
			bFileDialog.append2History(os.path.dirname(filename))

	#-----------------------------------------------------------------------
	def setStatus(self, msg, force_update=False):
		self.statusbar.configText(text=msg, fill="DarkBlue")
		if force_update:
			self.statusbar.update_idletasks()
			self.bufferbar.update_idletasks()

	#-----------------------------------------------------------------------
	# Set a status message from an event
	#-----------------------------------------------------------------------
	def updateStatus(self, event):
		self.setStatus(_(event.data))

	#-----------------------------------------------------------------------
	# Update canvas coordinates
	#-----------------------------------------------------------------------
	def updateCanvasCoords(self, event):
		x,y,z = event.data.split()
		self.statusx["text"] = "X: "+x
		self.statusy["text"] = "Y: "+y
		self.statusz["text"] = "Z: "+z

	#----------------------------------------------------------------------
	# Accept the user key if not editing any text
	#----------------------------------------------------------------------
	def acceptKey(self, skipRun=False):
		if not skipRun and self.running: return False
		focus = self.focus_get()
		if isinstance(focus, Entry) or \
		   isinstance(focus, Spinbox) or \
		   isinstance(focus, Listbox) or \
		   isinstance(focus, Text): return False
		return True

	#-----------------------------------------------------------------------
	def quit(self, event=None):
		if self.running and self._quit<1:
			tkMessageBox.showinfo(_("Running"),
				_("CNC is currently running, please stop it before."),
				parent=self)
			self._quit += 1
			return
		del self.widgets[:]

		if self.fileModified():
			return

		self.canvas.cameraOff()
		Sender.quit(self)
		self.saveConfig()
		self.destroy()
		if Utils.errors and Utils._errorReport:
			Utils.ReportDialog.sendErrorReport()
		tk.destroy()

	# ---------------------------------------------------------------------
	def configWidgets(self, var, value):
		for w in self.widgets:
			if isinstance(w,tuple):
				try:
					w[0].entryconfig(w[1], state=value)
				except TclError:
					pass
			elif isinstance(w,tkExtra.Combobox):
				w.configure(state=value)
			else:
				w[var] = value

	# ---------------------------------------------------------------------
	def busy(self):
		try:
			self.config(cursor="watch")
			self.update_idletasks()
		except TclError:
			pass

	# ----------------------------------------------------------------------
	def notBusy(self):
		try:
			self.config(cursor="")
		except TclError:
			pass

	# ---------------------------------------------------------------------
	def enable(self):
		self.configWidgets("state",NORMAL)
		self.statusbar.clear()
		self.statusbar.config(background="LightGray")
		self.bufferbar.clear()
		self.bufferbar.config(background="LightGray")
		self.bufferbar.setText("")

	# ---------------------------------------------------------------------
	def disable(self):
		self.configWidgets("state",DISABLED)

	# ----------------------------------------------------------------------
	# Check for updates
	# ----------------------------------------------------------------------
	def checkUpdates(self):
		# Find bCNC version
		Updates.CheckUpdateDialog(self, __version__)

	#-----------------------------------------------------------------------
	def loadShortcuts(self):
		for name, value in Utils.config.items("Shortcut"):
			# Convert to uppercase
			key = name.title()
			self.unbind("<%s>"%(key))	# unbind any possible old value
			if value:
				self.bind("<%s>"%(key), lambda e,s=self,c=value : s.execute(c))

	#-----------------------------------------------------------------------
	def showUserFile(self):
		webbrowser.open(Utils.iniUser)
		#os.startfile(Utils.iniUser)

	#-----------------------------------------------------------------------
	def loadConfig(self):
		global geometry

		if geometry is None:
			geometry = "%sx%s" % (Utils.getInt(Utils.__prg__, "width",  900),
					      Utils.getInt(Utils.__prg__, "height", 650))
		try: self.geometry(geometry)
		except: pass

		#restore windowsState
		try:
			self.wm_state(Utils.getStr(Utils.__prg__, "windowstate", "normal"))
		except:
			pass

		# read Tk fonts to initialize them
		font = Utils.getFont("TkDefaultFont")
		font = Utils.getFont("TkFixedFont")
		font = Utils.getFont("TkMenuFont")
		font = Utils.getFont("TkTextFont")

		self._swapKeyboard = Utils.getInt("Control", "swap", 0)

		self._onStart = Utils.getStr("Events", "onstart", "")
		self._onStop  = Utils.getStr("Events", "onstop",  "")

		tkExtra.Balloon.font = Utils.getFont("balloon", tkExtra.Balloon.font)

		Ribbon._FONT	= Utils.getFont("ribbon.label", Ribbon._FONT)
		Ribbon._TABFONT = Utils.getFont("ribbon.tab",	Ribbon._TABFONT)

		Ribbon._ACTIVE_COLOR	   = Utils.getStr("Color", "ribbon.active", Ribbon._ACTIVE_COLOR)
		Ribbon._LABEL_SELECT_COLOR = Utils.getStr("Color", "ribbon.select", Ribbon._LABEL_SELECT_COLOR)

		self.tools.loadConfig()
		Sender.loadConfig(self)
		self.loadShortcuts()

	#-----------------------------------------------------------------------
	def saveConfig(self):
		# Program
		Utils.setInt(Utils.__prg__,  "width",	 str(self.winfo_width()))
		Utils.setInt(Utils.__prg__,  "height",	 str(self.winfo_height()))
		#Utils.setInt(Utils.__prg__,  "x",	  str(self.winfo_rootx()))
		#Utils.setInt(Utils.__prg__,  "y",	  str(self.winfo_rooty()))
		Utils.setInt(Utils.__prg__,  "sash",	  str(self.paned.sash_coord(0)[0]))

		#save windowState
		Utils.setStr(Utils.__prg__,  "windowstate", str(self.wm_state()))
		Utils.setStr(Utils.__prg__,  "page",	 str(self.ribbon.getActivePage().name))

		# Connection
		Page.saveConfig()
		Sender.saveConfig(self)
		self.tools.saveConfig()
		self.canvasFrame.saveConfig()

	#-----------------------------------------------------------------------
	def loadHistory(self):
		try:
			f = open(Utils.hisFile,"r")
		except:
			return
		self.history = [x.strip() for x in f]
		self._historySearch = None
		f.close()

	#-----------------------------------------------------------------------
	def saveHistory(self):
		try:
			f = open(Utils.hisFile,"w")
		except:
			return
		f.write("\n".join(self.history))
		f.close()

	#-----------------------------------------------------------------------
	def cut(self, event=None):
		focus = self.focus_get()
		if focus in (self.canvas, self.editor):
			self.editor.cut()
			return "break"

	#-----------------------------------------------------------------------
	def copy(self, event=None):
		focus = self.focus_get()
		if focus in (self.canvas, self.editor):
			self.editor.copy()
			return "break"

	#-----------------------------------------------------------------------
	def paste(self, event=None):
		focus = self.focus_get()
		if focus in (self.canvas, self.editor):
			self.editor.paste()
			return "break"

	#-----------------------------------------------------------------------
	def undo(self, event=None):
		if not self.running and self.gcode.canUndo():
			self.gcode.undo();
			self.editor.fill()
			self.drawAfter()
		return "break"

	#-----------------------------------------------------------------------
	def redo(self, event=None):
		if not self.running and self.gcode.canRedo():
			self.gcode.redo();
			self.editor.fill()
			self.drawAfter()
		return "break"

	#-----------------------------------------------------------------------
	def addUndo(self, undoinfo):
		self.gcode.addUndo(undoinfo)

	#-----------------------------------------------------------------------
	def about(self, event=None, timer=None):
		toplevel = Toplevel(self)
		toplevel.transient(self)
		toplevel.title(_("About %s") % (Utils.__prg__))
		if sys.platform == "win32":
			self.iconbitmap("bCNC.ico")
		else:
			self.iconbitmap("@%s/bCNC.xbm"%(Utils.prgpath))

		bg = "#707070"
		fg = "#ffffff"

		font1 = 'Helvetica -32 bold'
		font2 = 'Helvetica -12'
		font3 = 'Helvetica -10'

		frame = Frame(toplevel, borderwidth=2,
				relief=SUNKEN, background=bg)
		frame.pack(side=TOP, expand=TRUE, fill=BOTH, padx=5, pady=5)

		# -----
		row = 0
		l = Label(frame, image=Utils.icons["bCNC"],
				foreground=fg, background=bg,
				relief=RAISED,
				padx=0, pady=0)
		l.grid(row=row, column=0, columnspan=2, padx=5, pady=5)

		# -----
		#row += 1
		#l = Label(frame, text=Utils.__prg__,
		#		foreground=fg, background=bg,
		#		font=font1)
		#l.grid(row=row, column=0, columnspan=2, sticky=W, padx=10, pady=5)

		# -----
		row += 1
		l = Label(frame, text=\
				_("bCNC/\tAn advanced fully featured\n" \
				  "\tg-code sender for GRBL."),
				font = font3,
				foreground=fg, background=bg, justify=LEFT)
		l.grid(row=row, column=0, columnspan=2, sticky=W, padx=10, pady=1)

		# -----
		row += 1
		f = Frame(frame, borderwidth=1, relief=SUNKEN,
			height=2, background=bg)
		f.grid(row=row, column=0, columnspan=2, sticky=EW, padx=5, pady=5)

		# -----
		row += 1
		l = Label(frame, text='www:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=E, padx=10, pady=2)

		l = Label(frame, text=Utils.__www__,
				foreground=fg, background=bg, justify=LEFT,
				activeforeground="Blue",
				font=font2, cursor="hand1")
		l.grid(row=row, column=1, sticky=W, padx=2, pady=2)
		l.bind('<Button-1>', lambda e : webbrowser.open(Utils.__www__))

		# -----
		row += 1
		l = Label(frame, text='email:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=E, padx=10, pady=2)

		l = Label(frame, text=__email__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=W, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='author:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=NE, padx=10, pady=2)

		l = Label(frame, text=__author__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='contributors:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=NE, padx=10, pady=2)

		l = Label(frame, text=Utils.__contribute__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='translations:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=NE, padx=10, pady=2)

		l = Label(frame, text=Utils.__translations__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='credits:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=NE, padx=10, pady=2)

		l = Label(frame, text=Utils.__credits__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='version:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=E, padx=10, pady=2)

		l = Label(frame, text=__version__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		# -----
		row += 1
		l = Label(frame, text='last change:',
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=0, sticky=E, padx=10, pady=2)

		l = Label(frame, text=__date__,
				foreground=fg, background=bg, justify=LEFT,
				font=font2)
		l.grid(row=row, column=1, sticky=NW, padx=2, pady=2)

		closeFunc = lambda e=None,t=toplevel: t.destroy()
		b = Button(toplevel, text=_("Close"), command=closeFunc)
		b.pack(pady=5)
		frame.grid_columnconfigure(1, weight=1)

		toplevel.bind('<Escape>',   closeFunc)
		toplevel.bind('<Return>',   closeFunc)
		toplevel.bind('<KP_Enter>', closeFunc)

		#Center to the screen
		#toplevel.update_idletasks()
		#w = toplevel.winfo_screenwidth()
		#h = toplevel.winfo_screenheight()
		#size = tuple(int(_) for _ in toplevel.geometry().split('+')[0].split('x'))
		#x = w/2 - size[0]/2
		#y = h/2 - size[1]/2
		#toplevel.geometry("%dx%d+%d+%d" % (size + (x, y)))

		toplevel.deiconify()
		toplevel.wait_visibility()
		toplevel.resizable(False, False)

		try: toplevel.grab_set()
		except: pass
		b.focus_set()
		toplevel.lift()
		if timer: toplevel.after(timer, closeFunc)
		toplevel.wait_window()

	#-----------------------------------------------------------------------
	def alarmClear(self, event=None):
		self._alarm = False

	#-----------------------------------------------------------------------
	# Display information on selected blocks
	#-----------------------------------------------------------------------
	def showInfo(self, event=None):
		self.canvas.showInfo(self.editor.getSelectedBlocks())
		return "break"

	#-----------------------------------------------------------------------
	# FIXME Very primitive
	#-----------------------------------------------------------------------
	def showStats(self, event=None):
		toplevel = Toplevel(self)
		toplevel.transient(self)
		toplevel.title(_("Statistics"))

		if CNC.inch:
			unit = "in"
		else:
			unit = "mm"

		# count enabled blocks
		e = 0
		l = 0
		r = 0
		t = 0
		for block in self.gcode.blocks:
			if block.enable:
				e += 1
				l += block.length
				r += block.rapid
				t += block.time

		# ===========
		frame = LabelFrame(toplevel, text=_("Enabled GCode"), foreground="DarkRed")
		frame.pack(fill=BOTH)

		# ---
		row, col = 0,0
		Label(frame, text=_("Margins X:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["xmin"], CNC.vars["xmax"],
			 CNC.vars["xmax"] -CNC.vars["xmin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text="... Y:").grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["ymin"], CNC.vars["ymax"],
			 CNC.vars["ymax"] -CNC.vars["ymin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text="... Z:").grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["zmin"], CNC.vars["zmax"],
			 CNC.vars["zmax"] -CNC.vars["zmin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("# Blocks:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text=str(e),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("Length:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g %s" % (l, unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("Rapid:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g %s" % (r, unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("Time:")).grid(row=row, column=col, sticky=E)
		col += 1
		h,m = divmod(t, 60)	# t in min
		s = (m-int(m))*60
		Label(frame, text="%d:%02d:%02d s" % (int(h),int(m),int(s)),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		frame.grid_columnconfigure(1, weight=1)


		# ===========
		frame = LabelFrame(toplevel, text=_("All GCode"), foreground="DarkRed")
		frame.pack(fill=BOTH)

		# ---
		row, col = 0,0
		Label(frame, text=_("Margins X:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["axmin"], CNC.vars["axmax"],
			 CNC.vars["axmax"] -CNC.vars["axmin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text="... Y:").grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["aymin"], CNC.vars["aymax"],
			 CNC.vars["aymax"] -CNC.vars["aymin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text="... Z:").grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g .. %g [%g] %s" % \
			(CNC.vars["azmin"], CNC.vars["azmax"],
			 CNC.vars["azmax"] -CNC.vars["azmin"],
			 unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("# Blocks:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text=str(len(self.gcode.blocks)),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)
		# ---
		row += 1
		col = 0
		Label(frame, text=_("Length:")).grid(row=row, column=col, sticky=E)
		col += 1
		Label(frame, text="%g %s" % (self.cnc.totalLength, unit),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		# ---
		row += 1
		col = 0
		Label(frame, text=_("Time:")).grid(row=row, column=col, sticky=E)
		col += 1
		h,m = divmod(self.cnc.totalTime, 60)	# t in min
		s = (m-int(m))*60
		Label(frame, text="%d:%02d:%02d s" % (int(h),int(m),int(s)),
			foreground="DarkBlue").grid(row=row, column=col, sticky=W)

		frame.grid_columnconfigure(1, weight=1)

		# ===========
		frame = Frame(toplevel)
		frame.pack(fill=X)

		closeFunc = lambda e=None,t=toplevel: t.destroy()
		b = Button(frame, text=_("Close"), command=closeFunc)
		b.pack(pady=5)
		frame.grid_columnconfigure(1, weight=1)

		toplevel.bind("<Escape>",    closeFunc)
		toplevel.bind("<Return>",    closeFunc)
		toplevel.bind("<KP_Enter>",  closeFunc)

		# ----
		toplevel.deiconify()
		toplevel.wait_visibility()
		toplevel.resizable(False, False)

		try: toplevel.grab_set()
		except: pass
		b.focus_set()
		toplevel.lift()
		toplevel.wait_window()

	#-----------------------------------------------------------------------
	def reportDialog(self, event=None):
		Utils.ReportDialog(self)

	#-----------------------------------------------------------------------
	def viewChange(self, event=None):
		if self.running:
			self._selectI = 0	# last selection pointer in items
		self.draw()

	# ----------------------------------------------------------------------
	def refresh(self, event=None):
		self.editor.fill()
		self.draw()

	# ----------------------------------------------------------------------
	def draw(self):
		view = CNCCanvas.VIEWS.index(self.canvasFrame.view.get())
		self.canvas.draw(view)
		self.selectionChange()

	# ----------------------------------------------------------------------
	# Redraw with a small delay
	# ----------------------------------------------------------------------
	def drawAfter(self, event=None):
		if self._drawAfter is not None: self.after_cancel(self._drawAfter)
		self._drawAfter = self.after(DRAW_AFTER, self.draw)
		return "break"
>>>>>>> no home button

print("This is currently broken. Use instead: python -m bCNC")

import os
import runpy

bcncpath = os.path.join(
	os.path.dirname(os.path.realpath(__file__)),
	'bCNC/__main__.py'
	)

print("bCNC runpy loader: %s"%(bcncpath))
runpy.run_path(bcncpath, run_name='__main__')
#runpy.run_module('bCNC', run_name='__main__', alter_sys=True)
