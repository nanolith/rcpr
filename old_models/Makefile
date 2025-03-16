.PHONY: model-check
MODEL_MAKEFILES?= \
	$(foreach file,\
	    $(wildcard *.mk),$(notdir $(file)))

.PHONY: ALL

ALL: $(MODEL_MAKEFILES:.mk=.foo)

%.foo : %.mk
	$(MAKE) -f $<
