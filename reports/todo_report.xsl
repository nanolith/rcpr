<?xml version="1.0"?>

<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<xsl:output method="text"/>
<xsl:strip-space elements="*"/>

<xsl:variable name="newline"><xsl:text>
</xsl:text></xsl:variable>

<xsl:template match="/">
    <xsl:apply-templates select="." mode="display">
        <xsl:with-param name="indent" select="'    '"/>
    </xsl:apply-templates>
    <xsl:text>Total: </xsl:text>
    <xsl:value-of select="round(10000.0 * count(.//item[@completed='true']) div count(.//item)) div 100.0"/>
    <xsl:text>%</xsl:text>
    <xsl:value-of select="$newline"/>
</xsl:template>

<xsl:template match="category" mode="display">
    <xsl:param name="indent" select="''"/>
    <xsl:value-of select="$indent"/>
    <xsl:value-of select="@name"/>
    <xsl:text>: </xsl:text>

    <xsl:value-of select="round(10000.0 * count(.//item[@completed='true']) div count(.//item)) div 100.0"/>
    <xsl:text>%</xsl:text>
    <xsl:value-of select="$newline"/>

    <xsl:apply-templates select="./category" mode="display">
        <xsl:with-param name="indent" select="concat($indent, '    ')"/>
    </xsl:apply-templates>
</xsl:template>

</xsl:stylesheet>
