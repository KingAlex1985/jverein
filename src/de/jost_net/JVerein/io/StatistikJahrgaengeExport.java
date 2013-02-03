/**********************************************************************
 * $Source$
 * $Revision$
 * $Date$
 * $Author$
 *
 * Copyright (c) by Heiner Jostkleigrewe
 * This program is free software: you can redistribute it and/or modify it under the terms of the 
 * GNU General Public License as published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,  but WITHOUT ANY WARRANTY; without 
 *  even the implied warranty of  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See 
 *  the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with this program.  If not, 
 * see <http://www.gnu.org/licenses/>.
 * 
 * heiner@jverein.de
 * www.jverein.de
 **********************************************************************/

package de.jost_net.JVerein.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Calendar;
import java.util.Date;
import java.util.TreeMap;

import com.itextpdf.text.DocumentException;

import de.jost_net.JVerein.Einstellungen;
import de.jost_net.JVerein.gui.control.MitgliedControl;
import de.jost_net.JVerein.rmi.Mitglied;
import de.jost_net.JVerein.server.MitgliedUtils;
import de.willuhn.datasource.rmi.DBIterator;
import de.willuhn.util.ProgressMonitor;

public abstract class StatistikJahrgaengeExport implements Exporter
{

  @Override
  public abstract String getName();

  @Override
  public abstract IOFormat[] getIOFormats(Class<?> objectType);

  protected File file;

  protected Date stichtag;

  protected TreeMap<String, StatistikJahrgang> statistik;

  @Override
  public void doExport(final Object[] objects, IOFormat format, File file,
      ProgressMonitor monitor) throws DocumentException, IOException
  {
    this.file = file;
    statistik = new TreeMap<String, StatistikJahrgang>();
    MitgliedControl control = (MitgliedControl) objects[0];
    stichtag = (Date) control.getStichtag().getValue();
    /*
     * Teil 1: nat�rliche Personen
     */
    DBIterator mitgl = Einstellungen.getDBService().createList(Mitglied.class);
    MitgliedUtils.setNurAktive(mitgl, stichtag);
    MitgliedUtils.setMitglied(mitgl);
    MitgliedUtils.setMitgliedNatuerlichePerson(mitgl);
    mitgl.addFilter("geburtsdatum is not null");
    mitgl.setOrder("order by geburtsdatum");
    Calendar cal = Calendar.getInstance();
    while (mitgl.hasNext())
    {
      Mitglied m = (Mitglied) mitgl.next();
      cal.setTime(m.getGeburtsdatum());
      String jg = cal.get(Calendar.YEAR) + "";
      StatistikJahrgang dsbj = statistik.get(jg);
      if (dsbj == null)
      {
        dsbj = new StatistikJahrgang();
        statistik.put(jg, dsbj);
      }
      dsbj.incrementGesamt();
      if (m.getGeschlecht().equals("m"))
      {
        dsbj.incrementMaennlich();
      }
      if (m.getGeschlecht().equals("w"))
      {
        dsbj.incrementWeiblich();
      }
    }
    /*
     * Teil 2: Juristische Personen
     */
    DBIterator mitglj = Einstellungen.getDBService().createList(Mitglied.class);
    MitgliedUtils.setNurAktive(mitglj, stichtag);
    MitgliedUtils.setMitglied(mitglj);
    MitgliedUtils.setMitgliedJuristischePerson(mitglj);
    while (mitglj.hasNext())
    {
      String jg = "juristische Personen";
      StatistikJahrgang dsbj = statistik.get(jg);
      if (dsbj == null)
      {
        dsbj = new StatistikJahrgang();
        statistik.put(jg, dsbj);
      }
      dsbj.incrementGesamt();
      mitglj.next();
    }

    open();
    close();
  }

  @Override
  public String getDateiname()
  {
    return "statistikjahrgaenge";
  }

  protected abstract void open() throws DocumentException,
      FileNotFoundException;

  protected abstract void close() throws IOException, DocumentException;

  public class StatistikJahrgang
  {

    private int anzahlgesamt = 0;

    private int anzahlmaennlich = 0;

    private int anzahlweiblich = 0;

    public int getAnzahlgesamt()
    {
      return anzahlgesamt;
    }

    public void incrementGesamt()
    {
      this.anzahlgesamt++;
    }

    public int getAnzahlmaennlich()
    {
      return anzahlmaennlich;
    }

    public void incrementMaennlich()
    {
      this.anzahlmaennlich++;
    }

    public int getAnzahlweiblich()
    {
      return anzahlweiblich;
    }

    public void incrementWeiblich()
    {
      this.anzahlweiblich++;
    }
  }

}