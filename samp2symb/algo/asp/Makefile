
# == CONFIGS ================================================================= #
# DIRECTORIES
D_BIN	?= bin

# GOALS
.DEFAULT_GOAL=all
.PHONY: all

all: $(D_BIN)/lp2normal2 $(D_BIN)/lp2acyc $(D_BIN)/lp2sat


# == DOWNLOAD ================================================================ #
# download last verions at https://research.ics.aalto.fi/software/asp/download/

$(D_BIN)/lp2normal:
	@mkdir -p $(dir $@)
	wget https://research.ics.aalto.fi/software/asp/lp2normal/binary-x86-64/lp2normal-1.14 -O $@
	chmod a+x $@

$(D_BIN)/lp2normal2:
	@mkdir -p $(dir $@)
	wget https://research.ics.aalto.fi/software/asp/lp2normal/binary-x86-64/lp2normal-2.27 -O $@
	chmod a+x $@

$(D_BIN)/lp2acyc:
	@mkdir -p $(dir $@)
	wget https://research.ics.aalto.fi/software/asp/download/binary-x86-64/lp2acyc-1.29 -O $@
	chmod a+x $@

$(D_BIN)/lp2sat:
	@mkdir -p $(dir $@)
	wget https://research.ics.aalto.fi/software/asp/download/binary-x86-64/lp2sat-1.24 -O $@
	chmod a+x $@

# == STANDARD TARGETS ======================================================== #
# https://www.gnu.org/prep/standards/html_node/Standard-Targets.html

.PHONY: clean mrproper nothing

clean:

mrproper: clean
	rm -rf -- $(D_BIN)/

distclean: mrproper

nothing:
	@# nothing to do